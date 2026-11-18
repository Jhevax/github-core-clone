// A standalone GitHub-compatible git forge: one process, Node 22 stdlib only.
// Serves git smart HTTP (upload-pack v2 + v0, receive-pack v0), REST v3,
// GraphQL v4 and MCP (streamable HTTP, revision 2026-07-28) from one in-memory
// store. No git binary, no network beyond the suite, no wall clock in any
// response that could reach a state export (timestamps are a deterministic
// counter from a fixed epoch).

import { createServer, type IncomingMessage, type Server, type ServerResponse } from 'node:http';
import { createHash } from 'node:crypto';
import { deflateSync, inflateSync } from 'node:zlib';

const JSON_TYPE = 'application/json; charset=utf-8';
const TOKEN = process.env.MAKEFUN_SHOP_TOKEN ?? '';
const ZERO_OID = '0'.repeat(40);
const EPOCH = 1735689600; // 2025-01-01T00:00:00Z; all served timestamps derive from it + a counter.

// ---------------------------------------------------------------- utilities
let seq = 0;
function nextSeq(): number { seq += 1; return seq; }
function isoNow(): string { return new Date((EPOCH + nextSeq()) * 1000).toISOString(); }
function sha1Hex(data: Buffer): string { return createHash('sha1').update(data).digest('hex'); }
function isOid(v: string): boolean { return /^[0-9a-f]{40}$/.test(v); }
function b64(buf: Buffer): string { return buf.toString('base64'); }
function b64dec(s: string): Buffer { return Buffer.from(s.replace(/[\r\n\t ]+/g, ''), 'base64'); }
function esc(s: string): string { return s; }

// ---------------------------------------------------------------- git objects
type ObjType = 'commit' | 'tree' | 'blob' | 'tag';
interface GitObj { type: ObjType; data: Buffer }
function hashObject(type: ObjType, data: Buffer): string {
  const h = createHash('sha1');
  h.update(Buffer.from(`${type} ${data.length}\0`, 'utf8'));
  h.update(data);
  return h.digest('hex');
}
interface TreeEntry { mode: string; name: string; oid: string }
function parseTree(data: Buffer): TreeEntry[] {
  const out: TreeEntry[] = [];
  let off = 0;
  while (off < data.length) {
    const sp = data.indexOf(0x20, off);
    const nul = data.indexOf(0x00, sp + 1);
    out.push({ mode: data.subarray(off, sp).toString('ascii'), name: data.subarray(sp + 1, nul).toString('utf8'), oid: data.subarray(nul + 1, nul + 21).toString('hex') });
    off = nul + 21;
  }
  return out;
}
function cmpTree(a: TreeEntry, b: TreeEntry): number {
  const l = Buffer.from(a.mode === '40000' ? `${a.name}/` : a.name, 'utf8');
  const r = Buffer.from(b.mode === '40000' ? `${b.name}/` : b.name, 'utf8');
  return Buffer.compare(l, r);
}
function buildTree(entries: TreeEntry[]): Buffer {
  const parts: Buffer[] = [];
  for (const e of [...entries].sort(cmpTree)) {
    parts.push(Buffer.from(`${e.mode} ${e.name}\0`, 'utf8'));
    parts.push(Buffer.from(e.oid, 'hex'));
  }
  return Buffer.concat(parts);
}
interface CommitView { tree: string; parents: string[]; author: string; committer: string; message: string }
function parseCommit(data: Buffer): CommitView {
  const blank = data.indexOf('\n\n');
  const head = blank < 0 ? data.toString('utf8') : data.subarray(0, blank).toString('utf8');
  const message = blank < 0 ? '' : data.subarray(blank + 2).toString('utf8');
  const v: CommitView = { tree: '', parents: [], author: '', committer: '', message };
  for (const line of head.split('\n')) {
    const sp = line.indexOf(' ');
    const k = sp < 0 ? line : line.slice(0, sp);
    const val = sp < 0 ? '' : line.slice(sp + 1);
    if (k === 'tree') v.tree = val;
    else if (k === 'parent') v.parents.push(val);
    else if (k === 'author') v.author = val;
    else if (k === 'committer') v.committer = val;
  }
  return v;
}
function parseTag(data: Buffer): { object: string; type: string; tag: string; tagger: string; message: string } {
  const blank = data.indexOf('\n\n');
  const head = blank < 0 ? data.toString('utf8') : data.subarray(0, blank).toString('utf8');
  const m = new Map<string, string>();
  for (const line of head.split('\n')) {
    const sp = line.indexOf(' ');
    if (sp > 0) m.set(line.slice(0, sp), line.slice(sp + 1));
  }
  return { object: m.get('object') ?? '', type: m.get('type') ?? '', tag: m.get('tag') ?? '', tagger: m.get('tagger') ?? '', message: blank < 0 ? '' : data.subarray(blank + 2).toString('utf8') };
}
function buildCommit(tree: string, parents: string[], author: string, message: string, ts: number): Buffer {
  const who = `${author} ${ts} +0000`;
  const lines = [`tree ${tree}`, ...parents.map((p) => `parent ${p}`), `author ${who}`, `committer ${who}`, ''];
  const msg = message.endsWith('\n') ? message : `${message}\n`;
  return Buffer.from(`${lines.join('\n')}\n${msg}`, 'utf8');
}

// Reachable closure: lookup(oid) -> GitObj | undefined.
function collectReachable(roots: Iterable<string>, lookup: (oid: string) => GitObj | undefined, allowMissing = false): Set<string> {
  const seen = new Set<string>();
  const stack = [...roots];
  while (stack.length) {
    const oid = stack.pop()!;
    if (seen.has(oid) || oid === ZERO_OID) continue;
    const obj = lookup(oid);
    if (!obj) { if (allowMissing) continue; throw new Error(`missing object ${oid}`); }
    seen.add(oid);
    if (obj.type === 'commit') {
      const c = parseCommit(obj.data);
      stack.push(c.tree);
      for (const p of c.parents) stack.push(p);
    } else if (obj.type === 'tree') {
      for (const e of parseTree(obj.data)) if (e.mode !== '160000') stack.push(e.oid);
    } else if (obj.type === 'tag') {
      stack.push(parseTag(obj.data).object);
    }
  }
  return seen;
}
// Flatten a tree (commit's tree) to path -> {oid, mode}.
function flattenTree(objects: Map<string, GitObj>, treeOid: string, prefix: string, out: Map<string, { oid: string; mode: string }>): void {
  const obj = objects.get(treeOid);
  if (!obj || obj.type !== 'tree') return;
  for (const e of parseTree(obj.data)) {
    const path = prefix ? `${prefix}/${e.name}` : e.name;
    if (e.mode === '40000') flattenTree(objects, e.oid, path, out);
    else out.set(path, { oid: e.oid, mode: e.mode });
  }
}
// Build nested trees from a flat path map; stores new tree objects in `store`.
function buildTreesFromFiles(store: Map<string, GitObj>, files: Map<string, { oid: string; mode: string }>): string {
  interface Node { files: Map<string, { oid: string; mode: string }>; dirs: Map<string, Node> }
  const mk = (): Node => ({ files: new Map(), dirs: new Map() });
  const root = mk();
  for (const [path, ent] of files) {
    const segs = path.split('/');
    let node = root;
    for (let i = 0; i < segs.length - 1; i++) {
      const s = segs[i]!;
      if (!node.dirs.has(s)) node.dirs.set(s, mk());
      node = node.dirs.get(s)!;
    }
    node.files.set(segs[segs.length - 1]!, ent);
  }
  const build = (node: Node): string => {
    const entries: TreeEntry[] = [];
    for (const [name, ent] of node.files) entries.push({ mode: ent.mode, name, oid: ent.oid });
    for (const [name, child] of node.dirs) entries.push({ mode: '40000', name, oid: build(child) });
    const data = buildTree(entries);
    const oid = hashObject('tree', data);
    if (!store.has(oid)) store.set(oid, { type: 'tree', data });
    return oid;
  };
  return build(root);
}
function putObj(store: Map<string, GitObj>, type: ObjType, data: Buffer): string {
  const oid = hashObject(type, data);
  if (!store.has(oid)) store.set(oid, { type, data });
  return oid;
}

// ---------------------------------------------------------------- packfiles
const TYPE_CODE: Record<ObjType, number> = { commit: 1, tree: 2, blob: 3, tag: 4 };
const CODE_TYPE: Record<number, ObjType> = { 1: 'commit', 2: 'tree', 3: 'blob', 4: 'tag' };
function writePackObjectHeader(type: ObjType, size: number): Buffer {
  const bytes: number[] = [];
  let rem = size;
  let first = (TYPE_CODE[type] << 4) | (rem & 0x0f);
  rem = Math.floor(rem / 16);
  while (rem > 0) { bytes.push(first | 0x80); first = rem & 0x7f; rem = Math.floor(rem / 128); }
  bytes.push(first);
  return Buffer.from(bytes);
}
function writePack(objects: GitObj[]): Buffer {
  const parts: Buffer[] = [];
  const header = Buffer.alloc(12);
  header.write('PACK', 0, 4, 'ascii');
  header.writeUInt32BE(2, 4);
  header.writeUInt32BE(objects.length, 8);
  parts.push(header);
  for (const o of objects) {
    parts.push(writePackObjectHeader(o.type, o.data.length));
    parts.push(deflateSync(o.data, { level: 1 }));
  }
  const body = Buffer.concat(parts);
  return Buffer.concat([body, createHash('sha1').update(body).digest()]);
}
function applyDelta(base: Buffer, delta: Buffer): Buffer {
  let off = 0;
  const readSize = (): number => {
    let v = 0; let sh = 0;
    for (;;) {
      const b = delta[off++]!;
      v += (b & 0x7f) * 2 ** sh; sh += 7;
      if (!(b & 0x80)) break;
    }
    return v;
  };
  const srcSize = readSize();
  const tgtSize = readSize();
  if (srcSize !== base.length) throw new Error('delta base size mismatch');
  const out = Buffer.allocUnsafe(tgtSize);
  let written = 0;
  while (off < delta.length) {
    const op = delta[off++]!;
    if (op & 0x80) {
      let co = 0; let cs = 0; let sh = 0;
      for (let bit = 0; bit < 4; bit++) { if (op & (1 << bit)) co += delta[off++]! * 2 ** sh; sh += 8; }
      sh = 0;
      for (let bit = 4; bit < 7; bit++) { if (op & (1 << bit)) cs += delta[off++]! * 2 ** sh; sh += 8; }
      if (cs === 0) cs = 0x10000;
      base.copy(out, written, co, co + cs);
      written += cs;
    } else if (op !== 0) {
      const n = op & 0x7f;
      delta.copy(out, written, off, off + n);
      off += n; written += n;
    } else throw new Error('delta opcode 0');
  }
  if (written !== tgtSize) throw new Error('delta size mismatch');
  return out;
}
interface RawPackEntry { offset: number; typeCode: number; size: number; data: Buffer; baseOffset?: number; baseOid?: string }
function readPack(pack: Buffer, resolveBase: (oid: string) => GitObj | undefined): Map<string, GitObj> {
  if (pack.length < 32 || pack.subarray(0, 4).toString('ascii') !== 'PACK') throw new Error('bad pack header');
  const version = pack.readUInt32BE(4);
  if (version !== 2 && version !== 3) throw new Error(`pack version ${version}`);
  const count = pack.readUInt32BE(8);
  const trailerStart = pack.length - 20;
  const raw: RawPackEntry[] = [];
  const byOffset = new Map<number, RawPackEntry>();
  let off = 12;
  const readVarint = (start: number): { size: number; next: number; first: number } => {
    let b = pack[start]!;
    const first = b;
    let size = b & 0x0f; let shift = 4; let o = start + 1;
    while (b & 0x80) { b = pack[o++]!; size += (b & 0x7f) * 2 ** shift; shift += 7; }
    return { size, next: o, first };
  };
  for (let i = 0; i < count; i++) {
    const entryOffset = off;
    const h = readVarint(off);
    off = h.next;
    const typeCode = (h.first >> 4) & 0x07;
    const entry: RawPackEntry = { offset: entryOffset, typeCode, size: h.size, data: Buffer.alloc(0) };
    if (typeCode === 6) {
      let b = pack[off]!; off += 1;
      let v = b & 0x7f;
      while (b & 0x80) { b = pack[off++]!; v = ((v + 1) * 128) + (b & 0x7f); }
      entry.baseOffset = entryOffset - v;
    } else if (typeCode === 7) {
      entry.baseOid = pack.subarray(off, off + 20).toString('hex');
      off += 20;
    } else if (!CODE_TYPE[typeCode]) throw new Error(`pack type ${typeCode}`);
    const inflated = inflateSync(pack.subarray(off, trailerStart), { info: true }) as unknown as { buffer: Buffer; engine: { bytesWritten: number } };
    if (inflated.buffer.length !== h.size) throw new Error('pack entry size mismatch');
    entry.data = inflated.buffer;
    off += inflated.engine.bytesWritten;
    raw.push(entry);
    byOffset.set(entryOffset, entry);
  }
  const objects = new Map<string, GitObj>();
  const resolved = new Map<number, { type: ObjType; data: Buffer; oid: string }>();
  const resolving = new Set<number>();
  const resolve = (entry: RawPackEntry): { type: ObjType; data: Buffer; oid: string } => {
    const cached = resolved.get(entry.offset);
    if (cached) return cached;
    if (resolving.has(entry.offset)) throw new Error('delta cycle');
    resolving.add(entry.offset);
    let result: { type: ObjType; data: Buffer; oid: string };
    if (entry.typeCode === 6) {
      const baseEntry = byOffset.get(entry.baseOffset!);
      let base: { type: ObjType; data: Buffer };
      if (baseEntry) base = resolve(baseEntry);
      else {
        // OFS base outside pack: cannot happen for a well-formed pack; treat as error.
        throw new Error('ofs-delta base outside pack');
      }
      const data = applyDelta(base.data, entry.data);
      result = { type: base.type, data, oid: hashObject(base.type, data) };
    } else if (entry.typeCode === 7) {
      let base: { type: ObjType; data: Buffer } | undefined;
      const inPack = raw.find((e) => {
        if (e.typeCode === 6 || e.typeCode === 7) return false;
        return hashObject(CODE_TYPE[e.typeCode]!, e.data) === entry.baseOid;
      });
      if (inPack) base = resolve(inPack);
      else base = resolveBase(entry.baseOid!);
      if (!base) throw new Error(`ref-delta base ${entry.baseOid} missing`);
      const data = applyDelta(base.data, entry.data);
      result = { type: base.type, data, oid: hashObject(base.type, data) };
    } else {
      const type = CODE_TYPE[entry.typeCode]!;
      result = { type, data: entry.data, oid: hashObject(type, entry.data) };
    }
    resolving.delete(entry.offset);
    resolved.set(entry.offset, result);
    objects.set(result.oid, { type: result.type, data: result.data });
    return result;
  };
  for (const e of raw) resolve(e);
  return objects;
}

// ---------------------------------------------------------------- pkt-line
function pktLine(payload: string | Buffer): Buffer {
  const body = typeof payload === 'string' ? Buffer.from(payload, 'utf8') : payload;
  const len = body.length + 4;
  return Buffer.concat([Buffer.from(len.toString(16).padStart(4, '0'), 'ascii'), body]);
}
const FLUSH = Buffer.from('0000', 'ascii');
const DELIM = Buffer.from('0001', 'ascii');
function pktLines(items: Array<string | Buffer | 'flush' | 'delim'>): Buffer {
  const parts: Buffer[] = [];
  for (const it of items) {
    if (it === 'flush') parts.push(FLUSH);
    else if (it === 'delim') parts.push(DELIM);
    else parts.push(pktLine(it));
  }
  return Buffer.concat(parts);
}
// Decode a pkt-line stream into {lines: string[], rest: Buffer} (rest = bytes after first flush).
function decodePktStream(buf: Buffer): { packets: Array<{ kind: 'data' | 'flush' | 'delim'; payload: Buffer }>; restOffset: number } {
  const packets: Array<{ kind: 'data' | 'flush' | 'delim'; payload: Buffer }> = [];
  let off = 0;
  while (off + 4 <= buf.length) {
    const len = parseInt(buf.subarray(off, off + 4).toString('ascii'), 16);
    if (Number.isNaN(len)) break;
    if (len === 0) { packets.push({ kind: 'flush', payload: Buffer.alloc(0) }); off += 4; break; }
    if (len === 1) { packets.push({ kind: 'delim', payload: Buffer.alloc(0) }); off += 4; continue; }
    if (len === 2) { off += 4; continue; }
    if (off + len > buf.length) break;
    packets.push({ kind: 'data', payload: buf.subarray(off + 4, off + len) });
    off += len;
  }
  return { packets, restOffset: off };
}
function pktTextLines(buf: Buffer): string[] {
  const { packets } = decodePktStream(buf);
  return packets.filter((p) => p.kind === 'data').map((p) => p.payload.toString('utf8'));
}

// ---------------------------------------------------------------- store
interface Label { name: string; color: string }
interface Issue {
  id: number; number: number; title: string; body: string; state: 'open' | 'closed';
  labels: Label[]; user: string; createdAt: string; updatedAt: string; seq: number;
}
interface Comment { id: number; body: string; user: string; createdAt: string }
interface Pull {
  id: number; number: number; title: string; body: string; state: 'open' | 'closed';
  head: string; base: string; headSha: string; baseSha: string; mergeBase: string;
  merged: boolean; mergedAt: string | null; mergeCommitSha: string | null; seq: number;
}
interface Repo {
  id: number; name: string; owner: string | null; isPrivate: boolean; description: string;
  defaultBranch: string; refs: Map<string, string>; objects: Map<string, GitObj>;
  issues: Map<number, Issue>; pulls: Map<number, Pull>; labels: Map<string, Label>;
  comments: Map<number, Comment[]>; nextNumber: number; nextCommentId: number;
  createdAt: string; version: number;
}
const reposByName = new Map<string, Repo>();
let nextRepoId = 5000;
let tokenOwner: string | null = null;
function viewerLogin(): string {
  if (tokenOwner) return tokenOwner;
  if (TOKEN && TOKEN.length <= 30 && /^[a-z][a-z0-9-]*$/i.test(TOKEN) && !/^[0-9a-f]{20,}$/i.test(TOKEN)) return TOKEN;
  return 'owner';
}
function learnOwner(owner: string): void {
  if (!owner) return;
  if (tokenOwner === null) {
    tokenOwner = owner;
    for (const r of reposByName.values()) if (r.owner === null) r.owner = owner;
  }
}
function touch(repo: Repo): void { repo.version += 1; fetchCache.clear(); }
// Resolve a repo by (owner segment, name); learns the token owner when the
// repo exists and the owner is still unknown. Returns null on 404.
function lookupRepo(ownerSeg: string, name: string): Repo | null {
  const repo = reposByName.get(name);
  if (!repo) return null;
  if (tokenOwner !== null) {
    if (ownerSeg !== tokenOwner) return null;
    if (repo.owner === null) repo.owner = tokenOwner;
    return repo;
  }
  if (repo.owner !== null && repo.owner !== ownerSeg) return null;
  learnOwner(ownerSeg);
  return repo;
}
function createRepo(name: string, isPrivate: boolean, description: string): Repo | null {
  if (reposByName.has(name)) return null;
  const repo: Repo = {
    id: nextRepoId++, name, owner: tokenOwner, isPrivate, description,
    defaultBranch: 'main', refs: new Map(), objects: new Map(),
    issues: new Map(), pulls: new Map(), labels: new Map(), comments: new Map(),
    nextNumber: 1, nextCommentId: 1, createdAt: isoNow(), version: 0,
  };
  reposByName.set(name, repo);
  return repo;
}
function repoOwner(repo: Repo): string { return repo.owner ?? viewerLogin(); }
function refTip(repo: Repo, ref: string): string | undefined { return repo.refs.get(ref); }
function branchTip(repo: Repo, branch: string): string | undefined { return repo.refs.get(`refs/heads/${branch}`); }
function isAncestor(repo: Repo, anc: string, desc: string): boolean {
  if (anc === desc) return true;
  const seen = new Set<string>();
  const stack = [desc];
  while (stack.length) {
    const oid = stack.pop()!;
    if (oid === anc) return true;
    if (seen.has(oid)) continue;
    seen.add(oid);
    const obj = repo.objects.get(oid);
    if (!obj || obj.type !== 'commit') continue;
    for (const p of parseCommit(obj.data).parents) stack.push(p);
  }
  return false;
}
function mergeBaseOf(repo: Repo, a: string, b: string): string {
  const ancA = new Set<string>();
  const stack = [a];
  while (stack.length) {
    const oid = stack.pop()!;
    if (ancA.has(oid)) continue;
    ancA.add(oid);
    const obj = repo.objects.get(oid);
    if (obj?.type === 'commit') for (const p of parseCommit(obj.data).parents) stack.push(p);
  }
  const stackB = [b];
  const seenB = new Set<string>();
  while (stackB.length) {
    const oid = stackB.pop()!;
    if (ancA.has(oid)) return oid;
    if (seenB.has(oid)) continue;
    seenB.add(oid);
    const obj = repo.objects.get(oid);
    if (obj?.type === 'commit') for (const p of parseCommit(obj.data).parents) stackB.push(p);
  }
  return '';
}
function filesAt(repo: Repo, commitOid: string): Map<string, { oid: string; mode: string }> {
  const out = new Map<string, { oid: string; mode: string }>();
  const obj = repo.objects.get(commitOid);
  if (!obj || obj.type !== 'commit') return out;
  flattenTree(repo.objects, parseCommit(obj.data).tree, '', out);
  return out;
}
function diffFiles(base: Map<string, { oid: string; mode: string }>, head: Map<string, { oid: string; mode: string }>): Array<{ path: string; status: string; oldOid: string | null; newOid: string | null }> {
  const out: Array<{ path: string; status: string; oldOid: string | null; newOid: string | null }> = [];
  const paths = new Set([...base.keys(), ...head.keys()]);
  for (const p of [...paths].sort()) {
    const b = base.get(p); const h = head.get(p);
    if (b && !h) out.push({ path: p, status: 'removed', oldOid: b.oid, newOid: null });
    else if (!b && h) out.push({ path: p, status: 'added', oldOid: null, newOid: h.oid });
    else if (b && h && b.oid !== h.oid) out.push({ path: p, status: 'modified', oldOid: b.oid, newOid: h.oid });
  }
  return out;
}
function countLines(repo: Repo, oid: string | null): number {
  if (!oid) return 0;
  const obj = repo.objects.get(oid);
  if (!obj) return 0;
  const text = obj.data.toString('utf8');
  if (text === '') return 0;
  return text.split('\n').length - (text.endsWith('\n') ? 1 : 0);
}
// Three-way squash merge: returns {conflict} or the merged file map.
function squashMerge(repo: Repo, pr: Pull, liveBaseSha?: string): { conflict: boolean; files: Map<string, { oid: string; mode: string }> } {
  const baseFiles = filesAt(repo, liveBaseSha ?? pr.baseSha);
  const headFiles = filesAt(repo, pr.headSha);
  const mbFiles = pr.mergeBase ? filesAt(repo, pr.mergeBase) : new Map<string, { oid: string; mode: string }>();
  const merged = new Map(baseFiles);
  let conflict = false;
  const paths = new Set([...mbFiles.keys(), ...headFiles.keys()]);
  for (const p of paths) {
    const mb = mbFiles.get(p); const h = headFiles.get(p); const b = baseFiles.get(p);
    const headChanged = (mb?.oid ?? null) !== (h?.oid ?? null);
    const baseChanged = (mb?.oid ?? null) !== (b?.oid ?? null);
    if (headChanged && baseChanged && (h?.oid ?? null) !== (b?.oid ?? null)) { conflict = true; continue; }
    if (headChanged) {
      if (h) merged.set(p, h); else merged.delete(p);
    }
  }
  return { conflict, files: merged };
}
function authorIdent(repo: Repo): string {
  const login = repoOwner(repo);
  return `${login} <${login}@example.invalid>`;
}
// Create a commit on `branch` applying `change` to the file map; returns commit oid.
function commitFiles(repo: Repo, branch: string, message: string, change: (files: Map<string, { oid: string; mode: string }>) => void): string {
  const tip = branchTip(repo, branch);
  const files = tip ? filesAt(repo, tip) : new Map<string, { oid: string; mode: string }>();
  change(files);
  const tree = buildTreesFromFiles(repo.objects, files);
  const ts = EPOCH + nextSeq();
  const data = buildCommit(tree, tip ? [tip] : [], authorIdent(repo), message, ts);
  const oid = putObj(repo.objects, 'commit', data);
  repo.refs.set(`refs/heads/${branch}`, oid);
  touch(repo);
  return oid;
}
function commitObjectFor(repo: Repo, oid: string): Record<string, unknown> | null {
  const obj = repo.objects.get(oid);
  if (!obj || obj.type !== 'commit') return null;
  const c = parseCommit(obj.data);
  const msg = c.message.replace(/\n$/, '');
  const parseWho = (who: string): { name: string; email: string; date: string } => {
    const m = /^(.*) <([^>]*)> (\d+) ([+-]\d{4})$/.exec(who);
    if (!m) return { name: who, email: '', date: isoNow() };
    return { name: m[1]!, email: m[2]!, date: new Date(Number(m[3]) * 1000).toISOString() };
  };
  const a = parseWho(c.author);
  const cm = parseWho(c.committer);
  return {
    sha: oid,
    commit: { message: msg, author: a, committer: cm, tree: { sha: c.tree } },
    author: { login: repoOwner(repo) },
    committer: { login: repoOwner(repo) },
    parents: c.parents.map((p) => ({ sha: p })),
  };
}
function listCommits(repo: Repo, fromOid: string | undefined): Record<string, unknown>[] {
  const out: Record<string, unknown>[] = [];
  if (!fromOid) return out;
  const seen = new Set<string>();
  const stack = [fromOid];
  while (stack.length) {
    const oid = stack.shift()!;
    if (seen.has(oid)) continue;
    seen.add(oid);
    const entry = commitObjectFor(repo, oid);
    if (!entry) continue;
    out.push(entry);
    const obj = repo.objects.get(oid)!;
    for (const p of parseCommit(obj.data).parents) stack.push(p);
  }
  return out;
}
function globalId(kind: string, ...parts: Array<string | number>): string {
  return Buffer.from(`${kind}:${parts.join(':')}`, 'utf8').toString('base64');
}
function parseGlobalId(id: string): { kind: string; parts: string[] } | null {
  try {
    const text = Buffer.from(id, 'base64').toString('utf8');
    const [kind, ...parts] = text.split(':');
    if (!kind || parts.length === 0) return null;
    return { kind, parts };
  } catch { return null; }
}
function repoJson(repo: Repo): Record<string, unknown> {
  const owner = repoOwner(repo);
  return {
    id: repo.id, node_id: globalId('Repository', repo.id), name: repo.name, full_name: `${owner}/${repo.name}`,
    owner: { login: owner, id: 1000, type: 'User' },
    private: repo.isPrivate, description: repo.description, default_branch: repo.defaultBranch,
    html_url: `https://example.invalid/${owner}/${repo.name}`, url: `/api/v3/repos/${owner}/${repo.name}`,
    clone_url: `https://example.invalid/${owner}/${repo.name}.git`, git_url: `git://example.invalid/${owner}/${repo.name}.git`,
    ssh_url: `git@example.invalid:${owner}/${repo.name}.git`,
    created_at: repo.createdAt, updated_at: repo.createdAt, pushed_at: repo.createdAt,
    has_issues: true, has_projects: false, has_wiki: false, has_pages: false, has_downloads: true,
    archived: false, disabled: false, fork: false, forks_count: 0, stargazers_count: 0, watchers_count: 0,
    open_issues_count: [...repo.issues.values()].filter((i) => i.state === 'open').length,
    license: null, permissions: { admin: true, maintain: true, push: true, triage: true, pull: true },
  };
}
function issueJson(repo: Repo, issue: Issue): Record<string, unknown> {
  const owner = repoOwner(repo);
  return {
    id: issue.id, node_id: globalId('Issue', repo.id, issue.number), number: issue.number,
    title: issue.title, body: issue.body, state: issue.state,
    user: { login: owner, id: 1000, type: 'User' },
    labels: issue.labels.map((l) => ({ id: 100000 + l.name.length, name: l.name, color: l.color, description: '' })),
    assignees: [], milestone: null, locked: false,
    comments: (repo.comments.get(issue.number) ?? []).length,
    created_at: issue.createdAt, updated_at: issue.updatedAt, closed_at: issue.state === 'closed' ? issue.updatedAt : null,
    html_url: `https://example.invalid/${owner}/${repo.name}/issues/${issue.number}`,
    url: `/api/v3/repos/${owner}/${repo.name}/issues/${issue.number}`,
    repository_url: `/api/v3/repos/${owner}/${repo.name}`,
  };
}
function pullJson(repo: Repo, pr: Pull): Record<string, unknown> {
  const owner = repoOwner(repo);
  return {
    id: pr.id, node_id: globalId('PullRequest', repo.id, pr.number), number: pr.number,
    title: pr.title, body: pr.body, state: pr.state,
    user: { login: owner, id: 1000, type: 'User' },
    head: { ref: pr.head, sha: pr.headSha, label: `${owner}:${pr.head}`, user: { login: owner } },
    base: { ref: pr.base, sha: pr.baseSha, label: `${owner}:${pr.base}`, user: { login: owner } },
    merged: pr.merged, mergeable: pr.merged ? false : true, mergeable_state: pr.merged ? 'unknown' : 'clean',
    merged_at: pr.mergedAt, merge_commit_sha: pr.mergeCommitSha,
    created_at: isoNow(), updated_at: isoNow(), closed_at: pr.state === 'closed' ? (pr.mergedAt ?? isoNow()) : null,
    html_url: `https://example.invalid/${owner}/${repo.name}/pull/${pr.number}`,
    url: `/api/v3/repos/${owner}/${repo.name}/pulls/${pr.number}`,
    draft: false, locked: false, comments: 0, review_comments: 0, commits: 1, additions: 0, deletions: 0, changed_files: 0,
  };
}

// ---------------------------------------------------------------- HTTP plumbing
let reqSeq = 0;
function sendJson(res: ServerResponse, status: number, body: unknown, extra: Record<string, string> = {}): void {
  const text = status === 204 ? '' : `${JSON.stringify(body)}\n`;
  res.writeHead(status, {
    'content-type': JSON_TYPE,
    'x-github-request-id': `req-${++reqSeq}`,
    ...(status === 204 ? {} : { 'content-length': Buffer.byteLength(text) }),
    ...extra,
  });
  res.end(text);
}
function sendRaw(res: ServerResponse, status: number, contentType: string, body: Buffer, extra: Record<string, string> = {}): void {
  res.writeHead(status, { 'content-type': contentType, 'content-length': body.length, ...extra });
  res.end(body);
}
function errJson(res: ServerResponse, status: number, message: string): void {
  sendJson(res, status, { message });
}
function readBody(req: IncomingMessage): Promise<Buffer> {
  return new Promise((resolve, reject) => {
    const chunks: Buffer[] = [];
    req.on('data', (c: Buffer) => chunks.push(c));
    req.on('end', () => resolve(Buffer.concat(chunks)));
    req.on('error', reject);
  });
}
function parseJsonBody(buf: Buffer): { ok: true; value: unknown } | { ok: false } {
  if (buf.length === 0) return { ok: true, value: {} };
  try { return { ok: true, value: JSON.parse(buf.toString('utf8')) }; } catch { return { ok: false }; }
}
function authed(req: IncomingMessage): boolean {
  if (TOKEN === '') {
    const h = req.headers.authorization ?? '';
    return h.startsWith('Bearer ') && h.slice(7).length > 0;
  }
  return (req.headers.authorization ?? '') === `Bearer ${TOKEN}`;
}
function queryOf(req: IncomingMessage): URLSearchParams {
  try { return new URL(req.url ?? '/', 'http://x').searchParams; } catch { return new URLSearchParams(); }
}
function pathOf(req: IncomingMessage): string {
  try { return decodeURIComponent(new URL(req.url ?? '/', 'http://x').pathname); } catch { return '/'; }
}
function pageParams(q: URLSearchParams): { page: number; perPage: number } {
  const perPage = Math.max(1, Math.min(100, Number(q.get('per_page') ?? '30') || 30));
  const page = Math.max(1, Number(q.get('page') ?? '1') || 1);
  return { page, perPage };
}
function absUrl(req: IncomingMessage, p: string): string {
  const host = req.headers.host ?? '127.0.0.1';
  return `http://${host}${p}`;
}
function pageLink(req: IncomingMessage, q: URLSearchParams, total: number): string | null {
  const { page, perPage } = pageParams(q);
  const totalPages = Math.max(1, Math.ceil(total / perPage));
  if (page >= totalPages) return null;
  const path = pathOf(req);
  return `<${absUrl(req, `${path}?page=${page + 1}&per_page=${perPage}`)}>; rel="next", <${absUrl(req, `${path}?page=${totalPages}&per_page=${perPage}`)}>; rel="last"`;
}

// ---------------------------------------------------------------- REST v3
async function handleRest(req: IncomingMessage, res: ServerResponse, path: string, method: string, rawBody: Buffer): Promise<boolean> {
  const q = queryOf(req);
  // Auth: every /api/v3 route except none requires the token.
  if (!authed(req)) { errJson(res, 401, 'Bad credentials'); return true; }
  const sub = path.slice('/api/v3'.length) || '/';
  const segs = sub.split('/').filter((s) => s !== '');
  const needJson = (method === 'POST' || method === 'PATCH' || method === 'PUT' || method === 'DELETE') && rawBody.length > 0;
  let body: unknown = {};
  if (needJson) {
    const parsed = parseJsonBody(rawBody);
    if (!parsed.ok) { errJson(res, 400, 'Problems parsing JSON'); return true; }
    body = parsed.value;
  }
  const b = (v: unknown): Record<string, unknown> => (v !== null && typeof v === 'object' && !Array.isArray(v) ? v as Record<string, unknown> : {});
  const str = (v: unknown): string => (typeof v === 'string' ? v : '');
  const bool = (v: unknown, dflt = false): boolean => (typeof v === 'boolean' ? v : dflt);

  // GET /api/v3/ and /api/v3
  if ((sub === '/' || sub === '') && method === 'GET') {
    sendJson(res, 200, { current_user_url: '/api/v3/user', rate_limit_url: '/api/v3/rate_limit', repository_url: '/api/v3/repos/{owner}/{repo}' }, { 'x-oauth-scopes': 'repo, read:org' });
    return true;
  }
  if (sub === '/meta' && method === 'GET') {
    sendJson(res, 200, { verifiable_password_authentication: true, installed_version: '1.0.0', hooks: [], git: [], pages: [] });
    return true;
  }
  if (sub === '/rate_limit' && method === 'GET') {
    sendJson(res, 200, { resources: { core: { limit: 5000, remaining: 4999, reset: 1735689600 } }, rate: { limit: 5000, remaining: 4999, reset: 1735689600 } });
    return true;
  }
  if (sub === '/user' && method === 'GET') {
    const login = viewerLogin();
    sendJson(res, 200, { login, id: 1000, node_id: globalId('User', 1000), type: 'User', name: login, email: `${login}@example.invalid`, html_url: `https://example.invalid/${login}` });
    return true;
  }
  // POST /user/repos ; GET /user/repos
  if (segs[0] === 'user' && segs[1] === 'repos') {
    if (method === 'POST') {
      const name = str(b(body).name);
      if (!name) { errJson(res, 422, 'name is required'); return true; }
      const repo = createRepo(name, bool(b(body).private, false), str(b(body).description));
      if (!repo) { errJson(res, 422, 'Repository already exists'); return true; }
      sendJson(res, 201, repoJson(repo));
      return true;
    }
    if (method === 'GET') {
      const owner = viewerLogin();
      const all = [...reposByName.values()].filter((r) => (r.owner ?? owner) === owner).sort((a, c) => a.id - c.id).map((r) => repoJson(r));
      const { page, perPage } = pageParams(q);
      const totalPages = Math.max(1, Math.ceil(all.length / perPage));
      const slice = all.slice((page - 1) * perPage, page * perPage);
      const extra: Record<string, string> = {};
      const link = pageLink(req, q, all.length);
      if (link) extra.link = link;
      sendJson(res, 200, slice, extra);
      return true;
    }
  }
  // /repos/{owner}/{repo}/...
  if (segs[0] === 'repos' && segs.length >= 3) {
    const ownerSeg = segs[1]!;
    const repoName = segs[2]!;
    const rest = segs.slice(3);
    // Repo lookup; learn owner from an existing repo read.
    const repo = lookupRepo(ownerSeg, repoName);
    if (!repo) { errJson(res, 404, 'Not Found'); return true; }
    if (rest.length === 0) {
      if (method === 'GET') { sendJson(res, 200, repoJson(repo)); return true; }
      if (method === 'PATCH') {
        if (typeof b(body).description === 'string') repo.description = b(body).description as string;
        if (typeof b(body).name === 'string' && b(body).name !== repo.name) {
          // rename: keep it simple, update the key
          reposByName.delete(repo.name);
          repo.name = b(body).name as string;
          reposByName.set(repo.name, repo);
        }
        sendJson(res, 200, repoJson(repo));
        return true;
      }
      if (method === 'DELETE') {
        reposByName.delete(repo.name);
        sendJson(res, 204, null);
        return true;
      }
      errJson(res, 404, 'Not Found'); return true;
    }
    const head = rest[0]!;
    // branches
    if (head === 'branches') {
      if (method === 'GET' && rest.length === 1) {
        const list = [...repo.refs.keys()].filter((r) => r.startsWith('refs/heads/')).sort()
          .map((r) => ({ name: r.slice('refs/heads/'.length), commit: { sha: repo.refs.get(r) }, protected: false }));
        sendJson(res, 200, list);
        return true;
      }
      if (method === 'GET' && rest.length === 2) {
        const tip = branchTip(repo, rest[1]!);
        if (!tip) { errJson(res, 404, 'Not Found'); return true; }
        sendJson(res, 200, { name: rest[1], commit: { sha: tip }, protected: false });
        return true;
      }
    }
    // commits
    if (head === 'commits' && method === 'GET' && rest.length === 1) {
      const shaParam = q.get('sha');
      let from: string | undefined;
      if (shaParam) from = branchTip(repo, shaParam) ?? (isOid(shaParam) ? shaParam : undefined);
      else from = branchTip(repo, repo.defaultBranch);
      sendJson(res, 200, listCommits(repo, from));
      return true;
    }
    // git/refs
    if (head === 'git' && rest[1] === 'refs') {
      if (method === 'POST' && rest.length === 2) {
        const ref = str(b(body).ref);
        const sha = str(b(body).sha);
        if (!ref.startsWith('refs/') || !isOid(sha) || !repo.objects.has(sha)) { errJson(res, 422, 'Invalid ref or sha'); return true; }
        if (repo.refs.has(ref)) { errJson(res, 422, 'Reference already exists'); return true; }
        repo.refs.set(ref, sha);
        touch(repo);
        sendJson(res, 201, { ref, object: { sha, type: repo.objects.get(sha)?.type ?? 'commit' }, url: `/api/v3/repos/${ownerSeg}/${repoName}/git/refs/${ref}` });
        return true;
      }
      if (method === 'GET') {
        const refPath = `refs/${rest.slice(2).join('/')}`;
        const tip = repo.refs.get(refPath);
        if (!tip) { errJson(res, 404, 'Not Found'); return true; }
        sendJson(res, 200, { ref: refPath, object: { sha: tip, type: repo.objects.get(tip)?.type ?? 'commit' } });
        return true;
      }
    }
    // contents
    if (head === 'contents') {
      const contentPath = rest.slice(1).join('/');
      const refParam = q.get('ref');
      const branch = typeof b(body).branch === 'string' ? (b(body).branch as string) : (refParam ?? repo.defaultBranch);
      if (method === 'GET') {
        const tip = branchTip(repo, branch);
        if (!tip) { errJson(res, 404, 'Not Found'); return true; }
        const files = filesAt(repo, tip);
        if (contentPath === '' || contentPath === undefined) {
          const entries = dirListing(repo, tip, '');
          sendJson(res, 200, entries);
          return true;
        }
        const file = files.get(contentPath);
        if (file) {
          const obj = repo.objects.get(file.oid)!;
          sendJson(res, 200, {
            type: 'file', encoding: 'base64', size: obj.data.length, name: contentPath.split('/').pop(),
            path: contentPath, sha: file.oid, content: b64(obj.data),
            url: `/api/v3/repos/${ownerSeg}/${repoName}/contents/${contentPath}`,
          });
          return true;
        }
        // directory?
        const prefix = `${contentPath}/`;
        const hasChild = [...files.keys()].some((p) => p.startsWith(prefix));
        if (hasChild) { sendJson(res, 200, dirListing(repo, tip, contentPath)); return true; }
        errJson(res, 404, 'Not Found'); return true;
      }
      if (method === 'PUT') {
        const message = str(b(body).message) || 'Update file';
        const contentB64 = str(b(body).content);
        if (!contentB64) { errJson(res, 422, 'content is required'); return true; }
        const data = b64dec(contentB64);
        const shaParam = typeof b(body).sha === 'string' ? (b(body).sha as string) : undefined;
        // branch may not exist yet: create it at the default tip
        if (!branchTip(repo, branch)) {
          const defTip = branchTip(repo, repo.defaultBranch);
          if (defTip) repo.refs.set(`refs/heads/${branch}`, defTip);
        }
        const tip = branchTip(repo, branch);
        const files = tip ? filesAt(repo, tip) : new Map<string, { oid: string; mode: string }>();
        const existing = files.get(contentPath);
        if (existing) {
          if (shaParam !== undefined && shaParam !== existing.oid) { errJson(res, 409, 'sha does not match'); return true; }
          if (shaParam === undefined) { errJson(res, 422, 'sha is required to update a file'); return true; }
        }
        const blobOid = putObj(repo.objects, 'blob', data);
        const commitSha = commitFiles(repo, branch, message, (f) => { f.set(contentPath, { oid: blobOid, mode: '100644' }); });
        sendJson(res, existing ? 200 : 201, {
          content: { name: contentPath.split('/').pop(), path: contentPath, sha: blobOid, size: data.length, encoding: 'base64', type: 'file' },
          commit: { sha: commitSha, message },
        });
        return true;
      }
      if (method === 'DELETE') {
        const shaParam = typeof b(body).sha === 'string' ? (b(body).sha as string) : undefined;
        const message = str(b(body).message) || 'Delete file';
        const tip = branchTip(repo, branch);
        if (!tip) { errJson(res, 404, 'Not Found'); return true; }
        const files = filesAt(repo, tip);
        const existing = files.get(contentPath);
        if (!existing) { errJson(res, 404, 'Not Found'); return true; }
        if (shaParam !== undefined && shaParam !== existing.oid) { errJson(res, 409, 'sha does not match'); return true; }
        const commitSha = commitFiles(repo, branch, message, (f) => { f.delete(contentPath); });
        sendJson(res, 200, { commit: { sha: commitSha, message } });
        return true;
      }
    }
    // labels
    if (head === 'labels') {
      if (method === 'POST' && rest.length === 1) {
        const name = str(b(body).name);
        const color = str(b(body).color) || 'ededed';
        if (!name) { errJson(res, 422, 'name is required'); return true; }
        const label: Label = { name, color };
        repo.labels.set(name, label);
        sendJson(res, 201, { id: 1000 + name.length, name, color, description: '' });
        return true;
      }
      if (method === 'GET' && rest.length === 1) {
        sendJson(res, 200, [...repo.labels.values()].map((l) => ({ id: 1000 + l.name.length, name: l.name, color: l.color })));
        return true;
      }
    }
    // issues
    if (head === 'issues') {
      if (rest.length === 1) {
        if (method === 'POST') {
          const title = str(b(body).title);
          const bodyText = str(b(body).body);
          const labelsIn = Array.isArray(b(body).labels) ? (b(body).labels as unknown[]) : [];
          const labels: Label[] = [];
          for (const l of labelsIn) {
            const name = typeof l === 'string' ? l : str((l as Record<string, unknown>)?.name);
            const found = repo.labels.get(name);
            if (!found) { errJson(res, 422, `Label does not exist: ${name}`); return true; }
            labels.push(found);
          }
          if (!title) { errJson(res, 422, 'title is required'); return true; }
          const number = repo.nextNumber++;
          const now = isoNow();
          const issue: Issue = { id: repo.id * 100000 + number, number, title, body: bodyText, state: 'open', labels, user: repoOwner(repo), createdAt: now, updatedAt: now, seq: nextSeq() };
          repo.issues.set(number, issue);
          sendJson(res, 201, issueJson(repo, issue));
          return true;
        }
        if (method === 'GET') {
          const state = q.get('state') ?? 'open';
          const sort = q.get('sort') ?? 'created';
          const direction = q.get('direction') ?? 'desc';
          let list = [...repo.issues.values()];
          if (state !== 'all') list = list.filter((i) => i.state === state);
          list.sort((a, c) => (direction === 'asc' ? a.number - c.number : c.number - a.number));
          void sort;
          const { page, perPage } = pageParams(q);
          const totalPages = Math.max(1, Math.ceil(list.length / perPage));
          const slice = list.slice((page - 1) * perPage, page * perPage).map((i) => issueJson(repo, i));
          const extra: Record<string, string> = {};
          const link = pageLink(req, q, list.length);
          if (link) extra.link = link;
          sendJson(res, 200, slice, extra);
          return true;
        }
      }
      const num = Number(rest[1]);
      if (Number.isInteger(num) && rest.length >= 2) {
        const issue = repo.issues.get(num);
        if (rest.length === 2) {
          if (!issue) { errJson(res, 404, 'Not Found'); return true; }
          if (method === 'GET') { sendJson(res, 200, issueJson(repo, issue)); return true; }
          if (method === 'PATCH') {
            if (typeof b(body).state === 'string') issue.state = (b(body).state as string) === 'closed' ? 'closed' : 'open';
            if (typeof b(body).title === 'string') issue.title = b(body).title as string;
            if (typeof b(body).body === 'string') issue.body = b(body).body as string;
            issue.updatedAt = isoNow();
            sendJson(res, 200, issueJson(repo, issue));
            return true;
          }
        }
        if (rest[2] === 'comments') {
          if (!issue) { errJson(res, 404, 'Not Found'); return true; }
          if (method === 'POST') {
            const cbody = str(b(body).body);
            const comment: Comment = { id: repo.nextCommentId++, body: cbody, user: repoOwner(repo), createdAt: isoNow() };
            const arr = repo.comments.get(num) ?? [];
            arr.push(comment);
            repo.comments.set(num, arr);
            sendJson(res, 201, { id: comment.id, node_id: globalId('Comment', repo.id, num, comment.id), body: cbody, user: { login: repoOwner(repo) }, created_at: comment.createdAt, updated_at: comment.createdAt });
            return true;
          }
          if (method === 'GET') {
            const arr = repo.comments.get(num) ?? [];
            sendJson(res, 200, arr.map((c) => ({ id: c.id, node_id: globalId('Comment', repo.id, num, c.id), body: c.body, user: { login: repoOwner(repo) }, created_at: c.createdAt, updated_at: c.createdAt })));
            return true;
          }
        }
      }
    }
    // pulls
    if (head === 'pulls') {
      if (rest.length === 1) {
        if (method === 'POST') {
          const title = str(b(body).title);
          const bodyText = str(b(body).body);
          const headRef = str(b(body).head).split(':').pop() ?? '';
          const baseRef = str(b(body).base).split(':').pop() ?? repo.defaultBranch;
          const headSha = branchTip(repo, headRef);
          const baseSha = branchTip(repo, baseRef);
          if (!headSha || !baseSha) { errJson(res, 422, 'head or base branch not found'); return true; }
          const existing = [...repo.pulls.values()].find((p) => p.head === headRef && p.base === baseRef && p.state === 'open');
          if (existing) { errJson(res, 422, 'A pull request already exists'); return true; }
          const number = repo.nextNumber++;
          const mb = mergeBaseOf(repo, headSha, baseSha);
          const pr: Pull = {
            id: repo.id * 100000 + number, number, title, body: bodyText, state: 'open',
            head: headRef, base: baseRef, headSha, baseSha, mergeBase: mb,
            merged: false, mergedAt: null, mergeCommitSha: null, seq: nextSeq(),
          };
          repo.pulls.set(number, pr);
          sendJson(res, 201, pullJson(repo, pr));
          return true;
        }
        if (method === 'GET') {
          const state = q.get('state') ?? 'open';
          let list = [...repo.pulls.values()];
          if (state !== 'all') list = list.filter((p) => p.state === state);
          list.sort((a, c) => a.number - c.number);
          const { page, perPage } = pageParams(q);
          const totalPages = Math.max(1, Math.ceil(list.length / perPage));
          const slice = list.slice((page - 1) * perPage, page * perPage).map((p) => pullJson(repo, p));
          const extra: Record<string, string> = {};
          const link = pageLink(req, q, list.length);
          if (link) extra.link = link;
          sendJson(res, 200, slice, extra);
          return true;
        }
      }
      const num = Number(rest[1]);
      if (Number.isInteger(num) && rest.length >= 2) {
        const pr = repo.pulls.get(num);
        if (rest.length === 2) {
          if (!pr) { errJson(res, 404, 'Not Found'); return true; }
          if (method === 'GET') { sendJson(res, 200, pullJson(repo, pr)); return true; }
        }
        if (rest[2] === 'files' && method === 'GET') {
          if (!pr) { errJson(res, 404, 'Not Found'); return true; }
          const mbFiles = pr.mergeBase ? filesAt(repo, pr.mergeBase) : new Map<string, { oid: string; mode: string }>();
          const headFiles = filesAt(repo, pr.headSha);
          const diffs = diffFiles(mbFiles, headFiles);
          sendJson(res, 200, diffs.map((d) => {
            const additions = d.status === 'removed' ? 0 : countLines(repo, d.newOid);
            const deletions = d.status === 'added' ? 0 : countLines(repo, d.oldOid);
            return {
              sha: d.newOid ?? d.oldOid, filename: d.path, status: d.status,
              additions, deletions, changes: additions + deletions,
              blob_url: '', raw_url: '', contents_url: '',
            };
          }));
          return true;
        }
        if (rest[2] === 'merge' && method === 'PUT') {
          if (!pr) { errJson(res, 404, 'Not Found'); return true; }
          if (pr.state === 'closed') { errJson(res, 405, 'Pull request is already merged or closed'); return true; }
          const merged = squashMerge(repo, pr, branchTip(repo, pr.base));
          if (merged.conflict) { errJson(res, 405, 'Merge conflict'); return true; }
          const tree = buildTreesFromFiles(repo.objects, merged.files);
          const baseTip = branchTip(repo, pr.base);
          const ts = EPOCH + nextSeq();
          const msg = `Merge pull request #${pr.number} from ${pr.head}`;
          const data = buildCommit(tree, baseTip ? [baseTip] : [], authorIdent(repo), msg, ts);
          const mergeSha = putObj(repo.objects, 'commit', data);
          repo.refs.set(`refs/heads/${pr.base}`, mergeSha);
          touch(repo);
          pr.state = 'closed';
          pr.merged = true;
          pr.mergedAt = isoNow();
          pr.mergeCommitSha = mergeSha;
          sendJson(res, 200, { sha: mergeSha, merged: true, message: 'Pull request successfully merged' });
          return true;
        }
      }
    }
    errJson(res, 404, 'Not Found');
    return true;
  }
  errJson(res, 404, 'Not Found');
  return true;
}
function dirListing(repo: Repo, tip: string, dirPath: string): Record<string, unknown>[] {
  const files = filesAt(repo, tip);
  const prefix = dirPath === '' ? '' : `${dirPath}/`;
  const seen = new Map<string, { type: string; sha: string }>();
  for (const [p, ent] of files) {
    if (!p.startsWith(prefix)) continue;
    const rest = p.slice(prefix.length);
    const seg = rest.split('/')[0]!;
    if (rest.includes('/')) {
      if (!seen.has(seg)) {
        // tree oid for this dir
        const dirFiles = new Map<string, { oid: string; mode: string }>();
        for (const [pp, ee] of files) if (pp.startsWith(`${prefix}${seg}/`)) dirFiles.set(pp.slice(prefix.length + seg.length + 1), ee);
        const treeOid = buildTreesFromFiles(repo.objects, dirFiles);
        seen.set(seg, { type: 'dir', sha: treeOid });
      }
    } else {
      seen.set(seg, { type: 'file', sha: ent.oid });
    }
  }
  return [...seen.entries()].sort((a, c) => (a[0] < c[0] ? -1 : 1)).map(([name, v]) => ({
    type: v.type, name, path: prefix + name, sha: v.sha, size: v.type === 'file' ? (repo.objects.get(v.sha)?.data.length ?? 0) : 0,
    url: `/api/v3/repos/${repoOwner(repo)}/${repo.name}/contents/${prefix}${name}`,
  }));
}

// ---------------------------------------------------------------- git smart HTTP
function peelToCommit(repo: Repo, oid: string): string {
  let cur = oid;
  for (let i = 0; i < 10; i++) {
    const obj = repo.objects.get(cur);
    if (!obj) return cur;
    if (obj.type === 'tag') cur = parseTag(obj.data).object;
    else return cur;
  }
  return cur;
}
function sortedRefs(repo: Repo): Array<[string, string]> {
  return [...repo.refs.entries()].sort((a, c) => (a[0] < c[0] ? -1 : 1));
}
function gitRepo(req: IncomingMessage, ownerSeg: string, repoName: string): Repo | null {
  const repo = reposByName.get(repoName);
  if (!repo) return null;
  if (tokenOwner !== null) {
    if (ownerSeg !== tokenOwner) return null;
    if (repo.owner === null) repo.owner = tokenOwner;
    return repo;
  }
  if (repo.owner !== null && repo.owner !== ownerSeg) return null;
  learnOwner(ownerSeg);
  return repo;
}
// v0 advertisement body.
function v0Advertisement(repo: Repo, service: 'git-upload-pack' | 'git-receive-pack'): Buffer {
  const headTip = branchTip(repo, repo.defaultBranch);
  const caps = service === 'git-upload-pack'
    ? 'side-band-64k thin-pack ofs-delta multi_ack shallow agent'
    : 'report-status side-band-64k delete-refs ofs-delta agent';
  const parts: Buffer[] = [];
  const lines: string[] = [];
  if (service === 'git-upload-pack') {
    parts.push(pktLine('# service=git-upload-pack\n'), FLUSH);
    if (headTip) lines.push(`${headTip} HEAD\0symref=HEAD:refs/heads/${repo.defaultBranch} ${caps}\n`);
    else lines.push(`${ZERO_OID} capabilities^{}\0${caps}\n`);
  } else {
    parts.push(pktLine('# service=git-receive-pack\n'), FLUSH);
    if (headTip) lines.push(`${headTip} HEAD\0${caps}\n`);
    else lines.push(`${ZERO_OID} capabilities^{}\0${caps}\n`);
  }
  for (const [name, oid] of sortedRefs(repo)) lines.push(`${oid} ${name}\n`);
  // peeled tags
  for (const [name, oid] of sortedRefs(repo)) {
    const obj = repo.objects.get(oid);
    if (name.startsWith('refs/tags/') && obj?.type === 'tag') {
      lines.push(`${peelToCommit(repo, oid)} ${name}^{}\n`);
    }
  }
  for (const l of lines) parts.push(pktLine(l));
  parts.push(FLUSH);
  return Buffer.concat(parts);
}
function v2Advertisement(): Buffer {
  return pktLines([
    'version 2\n',
    'agent=github-core-clone/1.0.0\n',
    'ls-refs=unborn\n',
    'fetch=shallow filter\n',
    'object-format=sha1\n',
    'server-option\n',
    'flush',
  ]);
}
function lsRefsLines(repo: Repo, opts: { peel: boolean; symrefs: boolean; prefixes: string[] }): string[] {
  const lines: string[] = [];
  const refs = sortedRefs(repo);
  const keep = (name: string): boolean => opts.prefixes.length === 0 || opts.prefixes.some((p) => name.startsWith(p));
  if (refs.length === 0) {
    if (keep('HEAD')) lines.push(`unborn HEAD symref-target:refs/heads/${repo.defaultBranch}\n`);
    return lines;
  }
  if (opts.symrefs && keep('HEAD')) {
    const headTip = branchTip(repo, repo.defaultBranch);
    if (headTip) lines.push(`${headTip} HEAD symref-target:refs/heads/${repo.defaultBranch}\n`);
  }
  for (const [name, oid] of refs) {
    if (!keep(name)) continue;
    let line = `${oid} ${name}`;
    const obj = repo.objects.get(oid);
    if (opts.peel && name.startsWith('refs/tags/') && obj?.type === 'tag') line += ` peeled:${peelToCommit(repo, oid)}`;
    lines.push(`${line}\n`);
  }
  return lines;
}
const fetchCache = new Map<string, Buffer>();
interface FetchPlan {
  objects: GitObj[]; shallow: string[]; unshallow: string[];
}
// Compute the objects to send for a fetch.
function planFetch(repo: Repo, wants: string[], haves: string[], shallowIn: string[], depth: number | null): FetchPlan {
  const lookup = (oid: string): GitObj | undefined => repo.objects.get(oid);
  const shallowSet = new Set(shallowIn);
  // Client-held objects: reachable from haves without crossing a shallow boundary's parents.
  const held = new Set<string>();
  {
    const stack = [...haves];
    const seenCommits = new Set<string>();
    while (stack.length) {
      const oid = stack.pop()!;
      if (held.has(oid)) continue;
      const obj = lookup(oid);
      if (!obj) continue;
      held.add(oid);
      if (obj.type === 'commit') {
        const c = parseCommit(obj.data);
        for (const x of collectReachable([c.tree], lookup, true)) held.add(x);
        if (!shallowSet.has(oid)) for (const p of c.parents) stack.push(p);
        void seenCommits;
      } else if (obj.type === 'tree') {
        for (const e of parseTree(obj.data)) stack.push(e.oid);
      } else if (obj.type === 'tag') stack.push(parseTag(obj.data).object);
    }
  }
  // Included commits with distances from wants.
  const dist = new Map<string, number>();
  const commitQueue: Array<[string, number]> = wants.map((w) => [w, 0] as [string, number]);
  const includedCommits = new Set<string>();
  while (commitQueue.length) {
    const [oid, d] = commitQueue.shift()!;
    if (dist.has(oid)) continue;
    const obj = lookup(oid);
    if (!obj || obj.type !== 'commit') continue;
    dist.set(oid, d);
    includedCommits.add(oid);
    if (depth === null || d + 1 < depth) {
      for (const p of parseCommit(obj.data).parents) commitQueue.push([p, d + 1]);
    }
  }
  const send = new Set<string>();
  for (const oid of includedCommits) {
    if (held.has(oid)) continue;
    // Add this commit + its tree closure (not parents).
    const obj = lookup(oid)!;
    send.add(oid);
    const c = parseCommit(obj.data);
    if (!held.has(c.tree)) {
      for (const x of collectReachable([c.tree], lookup, true)) if (!held.has(x)) send.add(x);
    }
  }
  // Non-depth fetches: include full closure of wants minus held.
  if (depth === null) {
    for (const x of collectReachable(wants, lookup, true)) if (!held.has(x)) send.add(x);
    // Tag objects reachable from wants that are not commits' closure: collectReachable covers tags via refs? wants are oids; tags pointing at wants are not reachable from wants. Include tag objects whose target is wanted: handled by caller via wants including tag oids (clone wants tag oids directly).
  }
  // Wants that are tag objects (a clone wants tag oids directly): send the tag
  // and its target closure (depth-limited to the tag's target commit only).
  for (const w of wants) {
    const obj = lookup(w);
    if (obj?.type === 'tag') {
      if (!held.has(w)) send.add(w);
      const target = parseTag(obj.data).object;
      const targetObj = lookup(target);
      if (targetObj?.type === 'commit') {
        if (depth === null) {
          for (const x of collectReachable([target], lookup, true)) if (!held.has(x)) send.add(x);
        } else if (!held.has(target)) {
          send.add(target);
          const c = parseCommit(targetObj.data);
          for (const x of collectReachable([c.tree], lookup, true)) if (!held.has(x)) send.add(x);
        }
      } else if (targetObj && !held.has(target)) send.add(target);
    }
  }
  const objects: GitObj[] = [];
  for (const oid of send) {
    const obj = lookup(oid);
    if (obj) objects.push(obj);
  }
  // Order: commits first (parents after children), then trees, then blobs — any order is valid; keep deterministic.
  const order: Record<string, number> = { commit: 0, tag: 1, tree: 2, blob: 3 };
  objects.sort((a, c) => (order[a.type] - order[c.type]) || (a.data.length - c.data.length));
  const shallow: string[] = [];
  const unshallow: string[] = [];
  if (depth !== null) {
    for (const oid of includedCommits) {
      const d = dist.get(oid)!;
      const obj = lookup(oid)!;
      const parents = parseCommit(obj.data).parents;
      if (d === depth - 1 && parents.length > 0) shallow.push(oid);
    }
    for (const s of shallowIn) {
      if (includedCommits.has(s)) {
        const parents = parseCommit(lookup(s)!.data).parents;
        if (parents.every((p) => includedCommits.has(p))) unshallow.push(s);
      }
    }
  }
  return { objects, shallow, unshallow };
}
function sidebandPack(pack: Buffer): Buffer {
  const parts: Buffer[] = [];
  const CHUNK = 60000;
  for (let off = 0; off < pack.length; off += CHUNK) {
    const slice = pack.subarray(off, Math.min(pack.length, off + CHUNK));
    parts.push(pktLine(Buffer.concat([Buffer.from([1]), slice])));
  }
  return Buffer.concat(parts);
}
async function handleGit(req: IncomingMessage, res: ServerResponse, path: string, method: string, rawBody: Buffer): Promise<boolean> {
  const m = /^\/([^/]+)\/([^/]+)\.git(\/.*)?$/.exec(path);
  if (!m) return false;
  const ownerSeg = m[1]!;
  const repoName = m[2]!;
  const restPath = m[3] ?? '';
  const q = queryOf(req);
  const service = q.get('service') ?? '';
  const gitProtocol = req.headers['git-protocol'] ?? '';
  const isV2 = gitProtocol === 'version=2' || gitProtocol === 'version=2\r' || String(gitProtocol).startsWith('version=2');

  // GET /info/refs
  if (method === 'GET' && restPath === '/info/refs') {
    const repo = gitRepo(req, ownerSeg, repoName);
    if (!repo) { sendRaw(res, 404, 'text/plain', Buffer.from('Not Found\n')); return true; }
    if (service === 'git-upload-pack') {
      if (isV2) {
        sendRaw(res, 200, 'application/x-git-upload-pack-advertisement', v2Advertisement());
      } else {
        sendRaw(res, 200, 'application/x-git-upload-pack-advertisement', v0Advertisement(repo, 'git-upload-pack'));
      }
      return true;
    }
    if (service === 'git-receive-pack') {
      sendRaw(res, 200, 'application/x-git-receive-pack-advertisement', v0Advertisement(repo, 'git-receive-pack'));
      return true;
    }
    sendRaw(res, 400, 'text/plain', Buffer.from('bad service\n'));
    return true;
  }
  // POST services
  if (method === 'POST' && (restPath === '/git-upload-pack' || restPath === '/git-receive-pack')) {
    const repo = gitRepo(req, ownerSeg, repoName);
    if (!repo) { sendRaw(res, 404, 'text/plain', Buffer.from('Not Found\n')); return true; }
    if (restPath === '/git-receive-pack') {
      handleReceivePack(repo, res, rawBody);
      return true;
    }
    // upload-pack
    if (isV2) { handleUploadPackV2(repo, res, rawBody); return true; }
    handleUploadPackV0(repo, res, rawBody);
    return true;
  }
  return false;
}
function handleUploadPackV2(repo: Repo, res: ServerResponse, rawBody: Buffer): void {
  const lines = pktTextLines(rawBody);
  if (lines.length === 0 || !lines[0]!.startsWith('command=')) {
    sendRaw(res, 400, 'application/x-git-upload-pack-result', Buffer.alloc(0));
    return;
  }
  const command = lines[0]!.slice('command='.length).trim();
  if (command === 'ls-refs') {
    const peel = lines.some((l) => l.trim() === 'peel');
    const symrefs = lines.some((l) => l.trim() === 'symrefs');
    const prefixes = lines.filter((l) => l.startsWith('ref-prefix ')).map((l) => l.slice('ref-prefix '.length).trim());
    const out = lsRefsLines(repo, { peel, symrefs, prefixes });
    const parts: Buffer[] = [];
    for (const l of out) parts.push(pktLine(l));
    parts.push(FLUSH);
    sendRaw(res, 200, 'application/x-git-upload-pack-result', Buffer.concat(parts));
    return;
  }
  if (command === 'fetch') {
    const wants: string[] = [];
    const haves: string[] = [];
    const shallowIn: string[] = [];
    let depth: number | null = null;
    for (const l of lines.slice(1)) {
      const t = l.trim();
      if (t.startsWith('want ')) wants.push(t.slice(5).trim());
      else if (t.startsWith('have ')) haves.push(t.slice(5).trim());
      else if (t.startsWith('shallow ')) shallowIn.push(t.slice(8).trim());
      else if (t.startsWith('deepen ')) depth = Number(t.slice(7).trim());
    }
    const cacheKey = `v2|${repo.id}|${repo.version}|${wants.join(',')}|${haves.join(',')}|${shallowIn.join(',')}|${depth}`;
    const cached = fetchCache.get(cacheKey);
    if (cached) { sendRaw(res, 200, 'application/x-git-upload-pack-result', cached); return; }
    const plan = planFetch(repo, wants, haves, shallowIn, depth);
    const parts: Buffer[] = [];
    // Protocol v2: sections are separated by DELIM (0001); the response ends
    // with FLUSH (0000). A flush after the ack section makes real git treat
    // the response as finished ("expected response end packet").
    const hasPack = plan.objects.length > 0;
    const hasShallowInfo = depth !== null && (plan.shallow.length > 0 || plan.unshallow.length > 0);
    if (haves.length > 0) {
      parts.push(pktLine('acknowledgments\n'));
      const acked = haves.filter((h) => repo.objects.has(h));
      if (acked.length > 0) {
        for (const h of acked) parts.push(pktLine(`ACK ${h}\n`));
        parts.push(pktLine('ready\n'));
      } else {
        parts.push(pktLine('NAK\n'));
      }
      parts.push(hasPack || hasShallowInfo ? DELIM : FLUSH);
    }
    if (hasShallowInfo) {
      parts.push(pktLine('shallow-info\n'));
      for (const s of plan.shallow) parts.push(pktLine(`shallow ${s}\n`));
      for (const s of plan.unshallow) parts.push(pktLine(`unshallow ${s}\n`));
      parts.push(hasPack ? DELIM : FLUSH);
    }
    if (hasPack) {
      const pack = writePack(plan.objects);
      parts.push(pktLine('packfile\n'));
      parts.push(sidebandPack(pack));
      parts.push(FLUSH);
    }
    const body = Buffer.concat(parts);
    if (fetchCache.size > 200) fetchCache.clear();
    fetchCache.set(cacheKey, body);
    sendRaw(res, 200, 'application/x-git-upload-pack-result', body);
    return;
  }
  sendRaw(res, 400, 'application/x-git-upload-pack-result', Buffer.alloc(0));
}
function decodeAllPackets(buf: Buffer): Array<{ kind: 'data' | 'flush' | 'delim'; payload: Buffer }> {
  const packets: Array<{ kind: 'data' | 'flush' | 'delim'; payload: Buffer }> = [];
  let off = 0;
  while (off + 4 <= buf.length) {
    const len = parseInt(buf.subarray(off, off + 4).toString('ascii'), 16);
    if (Number.isNaN(len)) break;
    if (len === 0) { packets.push({ kind: 'flush', payload: Buffer.alloc(0) }); off += 4; continue; }
    if (len === 1) { packets.push({ kind: 'delim', payload: Buffer.alloc(0) }); off += 4; continue; }
    if (len === 2) { off += 4; continue; }
    if (off + len > buf.length) break;
    packets.push({ kind: 'data', payload: buf.subarray(off + 4, off + len) });
    off += len;
  }
  return packets;
}
function handleUploadPackV0(repo: Repo, res: ServerResponse, rawBody: Buffer): void {
  const packets = decodeAllPackets(rawBody);
  const lines = packets.filter((p) => p.kind === 'data').map((p) => p.payload.toString('utf8'));
  if (lines.length === 0) {
    sendRaw(res, 400, 'application/x-git-upload-pack-result', Buffer.alloc(0));
    return;
  }
  const wants: string[] = [];
  const haves: string[] = [];
  const shallowIn: string[] = [];
  let depth: number | null = null;
  let section = 0;
  for (const raw of lines) {
    const t = raw.trim();
    if (t.startsWith('want ')) wants.push(t.slice(5).split(' ')[0]!);
    else if (t.startsWith('shallow ')) shallowIn.push(t.slice(8).trim());
    else if (t.startsWith('deepen ')) depth = Number(t.slice(7).trim());
    else if (t.startsWith('have ')) haves.push(t.slice(5).trim());
    void section;
  }
  // v0 splits wants and haves by a flush; our pktTextLines already flattened both sections, fine.
  const cacheKey = `v0|${repo.id}|${repo.version}|${wants.join(',')}|${haves.join(',')}|${shallowIn.join(',')}|${depth}`;
  const cached = fetchCache.get(cacheKey);
  if (cached) { sendRaw(res, 200, 'application/x-git-upload-pack-result', cached); return; }
  const plan = planFetch(repo, wants, haves, shallowIn, depth);
  const parts: Buffer[] = [];
  parts.push(pktLine('NAK\n'));
  for (const s of plan.shallow) parts.push(pktLine(`shallow ${s}\n`));
  for (const s of plan.unshallow) parts.push(pktLine(`unshallow ${s}\n`));
  if (plan.objects.length > 0) {
    const pack = writePack(plan.objects);
    parts.push(sidebandPack(pack));
  }
  parts.push(FLUSH);
  const body = Buffer.concat(parts);
  if (fetchCache.size > 200) fetchCache.clear();
  fetchCache.set(cacheKey, body);
  sendRaw(res, 200, 'application/x-git-upload-pack-result', body);
}
function handleReceivePack(repo: Repo, res: ServerResponse, rawBody: Buffer): void {
  const { packets, restOffset } = decodePktStream(rawBody);
  const cmdLines = packets.filter((p) => p.kind === 'data').map((p) => p.payload.toString('utf8'));
  const commands: Array<{ oldOid: string; newOid: string; ref: string }> = [];
  for (const raw of cmdLines) {
    const line = raw.replace(/\n$/, '');
    const nul = line.indexOf('\0');
    const head = nul >= 0 ? line.slice(0, nul) : line;
    const parts = head.split(' ');
    if (parts.length >= 3 && isOid(parts[0]!) && isOid(parts[1]!)) {
      commands.push({ oldOid: parts[0]!, newOid: parts[1]!, ref: parts[2]! });
    }
  }
  let unpackOk = true;
  let unpackDetail = 'ok';
  const packBytes = rawBody.subarray(restOffset);
  const hasUpdate = commands.some((c) => c.newOid !== ZERO_OID);
  if (hasUpdate && packBytes.length > 0) {
    try {
      const objects = readPack(packBytes, (oid) => repo.objects.get(oid));
      for (const [oid, obj] of objects) if (!repo.objects.has(oid)) repo.objects.set(oid, obj);
    } catch (err) {
      unpackOk = false;
      unpackDetail = err instanceof Error ? err.message : 'unpack failed';
    }
  } else if (hasUpdate && packBytes.length === 0) {
    unpackOk = false;
    unpackDetail = 'unpacker error: empty pack';
  }
  if (unpackOk) touch(repo);
  const reportLines: string[] = [];
  reportLines.push(unpackOk ? 'unpack ok\n' : `unpack ${unpackDetail}\n`);
  for (const cmd of commands) {
    if (!unpackOk) { reportLines.push(`ng ${cmd.ref} unpack failed\n`); continue; }
    const current = repo.refs.get(cmd.ref);
    if (cmd.newOid === ZERO_OID) {
      // delete
      if (current === undefined) reportLines.push(`ng ${cmd.ref} no such ref\n`);
      else if (cmd.oldOid !== ZERO_OID && cmd.oldOid !== current) reportLines.push(`ng ${cmd.ref} non-fast-forward\n`);
      else { repo.refs.delete(cmd.ref); reportLines.push(`ok ${cmd.ref}\n`); }
      continue;
    }
    const newObj = repo.objects.get(cmd.newOid);
    if (!newObj) { reportLines.push(`ng ${cmd.ref} missing object\n`); continue; }
    if (current === undefined) {
      if (cmd.oldOid !== ZERO_OID) { reportLines.push(`ng ${cmd.ref} non-fast-forward\n`); continue; }
      repo.refs.set(cmd.ref, cmd.newOid);
      reportLines.push(`ok ${cmd.ref}\n`);
      continue;
    }
    if (cmd.oldOid !== current) { reportLines.push(`ng ${cmd.ref} non-fast-forward\n`); continue; }
    if (cmd.newOid === current) { reportLines.push(`ok ${cmd.ref}\n`); continue; }
    // fast-forward check: new must descend from old (for commits); tags: allow if different object? git requires FF for tags too unless forced; treat non-descendant as non-fast-forward for commits, and for non-commit objects allow only if old is ancestor... simplify: if new is commit and old is commit, require isAncestor.
    const newIsCommit = newObj.type === 'commit';
    const oldObj = repo.objects.get(current);
    if (newIsCommit && oldObj?.type === 'commit') {
      if (!isAncestor(repo, current, cmd.newOid)) { reportLines.push(`ng ${cmd.ref} non-fast-forward\n`); continue; }
    } else if (newObj.type === 'tag' && oldObj?.type === 'tag') {
      // tag update to a different tag object: refuse unless it peels to a descendant
      const newCommit = peelToCommit(repo, cmd.newOid);
      const oldCommit = peelToCommit(repo, current);
      if (!isAncestor(repo, oldCommit, newCommit)) { reportLines.push(`ng ${cmd.ref} non-fast-forward\n`); continue; }
    }
    repo.refs.set(cmd.ref, cmd.newOid);
    reportLines.push(`ok ${cmd.ref}\n`);
  }
  // The report-status stream inside band 1 must itself end with a flush
  // pkt-line (real git's receive_status reads until an inner flush; without
  // it the client sees EOF and reports "remote end hung up").
  const reportBody = Buffer.concat([pktLines(reportLines.map((l) => l as string)), FLUSH]);
  // Wrap report in sideband band 1.
  const parts: Buffer[] = [];
  const CHUNK = 60000;
  for (let off = 0; off < reportBody.length; off += CHUNK) {
    const slice = reportBody.subarray(off, Math.min(reportBody.length, off + CHUNK));
    parts.push(pktLine(Buffer.concat([Buffer.from([1]), slice])));
  }
  parts.push(FLUSH);
  sendRaw(res, 200, 'application/x-git-receive-pack-result', Buffer.concat(parts));
}

// ---------------------------------------------------------------- GraphQL v4
// Minimal parser for the documents gh / github-mcp-server send: operations,
// variables, aliases, arguments (literals, variables, enums, input objects,
// lists, null), inline fragments, __type.
type GqlValue = string | number | boolean | null | GqlValue[] | { [k: string]: GqlValue };
interface GqlField {
  alias: string | null; name: string; args: Record<string, GqlValue>;
  children: GqlField[]; inlineType: string | null;
}
interface GqlOp { kind: 'query' | 'mutation'; name: string | null; fields: GqlField[] }
function tokenizeGql(src: string): string[] {
  const toks: string[] = [];
  let i = 0;
  while (i < src.length) {
    const c = src[i]!;
    if (/\s/.test(c) || c === ',') { i++; continue; }
    if (c === '#') { while (i < src.length && src[i] !== '\n') i++; continue; }
    if (c === '.' && src.slice(i, i + 3) === '...') { toks.push('...'); i += 3; continue; }
    if ('{}()[]:!=$'.includes(c)) { toks.push(c); i++; continue; }
    if (c === '"') {
      let j = i + 1; let out = '';
      while (j < src.length && src[j] !== '"') { if (src[j] === '\\' && j + 1 < src.length) { out += src[j + 1]; j += 2; } else { out += src[j]; j++; } }
      toks.push(JSON.stringify(out));
      i = j + 1; continue;
    }
    let j = i;
    while (j < src.length && /[A-Za-z0-9_\-.]/.test(src[j]!)) j++;
    toks.push(src.slice(i, j));
    i = j;
  }
  return toks;
}
class GqlParser {
  toks: string[]; pos = 0;
  constructor(src: string) { this.toks = tokenizeGql(src); }
  peek(): string { return this.toks[this.pos] ?? ''; }
  next(): string { return this.toks[this.pos++] ?? ''; }
  expect(t: string): void { if (this.next() !== t) throw new Error(`expected ${t}`); }
  parseValue(vars: Record<string, unknown>): GqlValue {
    const t = this.next();
    if (t === '$') { const name = this.next(); const v = vars[name]; return gqlFromJson(v); }
    if (t === '{') {
      const obj: Record<string, GqlValue> = {};
      while (this.peek() !== '}') { const k = this.next(); this.expect(':'); obj[k] = this.parseValue(vars); }
      this.expect('}');
      return obj;
    }
    if (t === '[') {
      const arr: GqlValue[] = [];
      while (this.peek() !== ']') arr.push(this.parseValue(vars));
      this.expect(']');
      return arr;
    }
    if (t.startsWith('"')) return JSON.parse(t) as string;
    if (t === 'true') return true;
    if (t === 'false') return false;
    if (t === 'null') return null;
    const n = Number(t);
    if (t !== '' && !Number.isNaN(n)) return n;
    return t; // enum as string
  }
  parseArgs(vars: Record<string, unknown>): Record<string, GqlValue> {
    const args: Record<string, GqlValue> = {};
    if (this.peek() !== '(') return args;
    this.expect('(');
    while (this.peek() !== ')') { const k = this.next(); this.expect(':'); args[k] = this.parseValue(vars); }
    this.expect(')');
    return args;
  }
  parseSelection(vars: Record<string, unknown>): GqlField[] {
    this.expect('{');
    const fields: GqlField[] = [];
    while (this.peek() !== '}') {
      if (this.peek() === '...') {
        this.next();
        let inlineType: string | null = null;
        if (this.peek() === 'on') { this.next(); inlineType = this.next(); }
        else { this.next(); /* fragment name: unsupported, skip its selection */ }
        const children = this.parseSelection(vars);
        fields.push({ alias: null, name: '__fragment', args: {}, children, inlineType });
        continue;
      }
      const first = this.next();
      let alias: string | null = null;
      let name = first;
      if (this.peek() === ':') { this.next(); alias = first; name = this.next(); }
      const args = this.parseArgs(vars);
      const children = this.peek() === '{' ? this.parseSelection(vars) : [];
      fields.push({ alias, name, args, children, inlineType: null });
    }
    this.expect('}');
    return fields;
  }
  parseOperation(vars: Record<string, unknown>): GqlOp {
    let kind: 'query' | 'mutation' = 'query';
    let name: string | null = null;
    const t = this.peek();
    if (t === 'query' || t === 'mutation') { kind = this.next() as 'query' | 'mutation'; if (this.peek() !== '(' && this.peek() !== '{' && this.peek() !== '') name = this.next(); }
    if (this.peek() === '(') {
      // variable definitions: skip balanced parens
      let depth = 0;
      do { const tok = this.next(); if (tok === '(') depth++; else if (tok === ')') depth--; } while (depth > 0);
    }
    const fields = this.parseSelection(vars);
    return { kind, name, fields };
  }
}
function gqlFromJson(v: unknown): GqlValue {
  if (v === null || v === undefined) return null;
  if (typeof v === 'string' || typeof v === 'number' || typeof v === 'boolean') return v;
  if (Array.isArray(v)) return v.map(gqlFromJson);
  if (typeof v === 'object') {
    const out: Record<string, GqlValue> = {};
    for (const [k, val] of Object.entries(v as Record<string, unknown>)) out[k] = gqlFromJson(val);
    return out;
  }
  return null;
}
const ISSUE_FIELDS = ['id', 'number', 'title', 'state', 'body', 'url', 'createdAt', 'updatedAt'];
const PR_FIELDS = ['id', 'number', 'title', 'state', 'body', 'headRefName', 'baseRefName', 'mergeable', 'merged', 'files', 'url', 'createdAt'];
const REPO_FIELDS = ['id', 'databaseId', 'name', 'nameWithOwner', 'owner', 'defaultBranchRef', 'viewerPermission', 'hasIssuesEnabled', 'issue', 'issues', 'pullRequests', 'pullRequest', 'url'];
const TYPE_FIELDS: Record<string, string[]> = {
  Issue: [...ISSUE_FIELDS, 'labels', 'comments'],
  PullRequest: [...PR_FIELDS, 'headRefOid', 'baseRefOid', 'mergeCommit', 'author'],
  Repository: REPO_FIELDS,
  User: ['login', 'id', 'name'],
  SearchType: [],
  IssueConnection: ['nodes', 'pageInfo', 'totalCount'],
  PullRequestConnection: ['nodes', 'pageInfo', 'totalCount'],
  IssueState: [], OrderDirection: [], IssueOrderField: [],
};
const TYPE_ENUMS: Record<string, string[]> = {
  SearchType: ['ISSUE', 'REPOSITORY', 'USER', 'DISCUSSION'],
  IssueState: ['OPEN', 'CLOSED'],
  PullRequestState: ['OPEN', 'CLOSED', 'MERGED'],
  MergeableState: ['MERGEABLE', 'CONFLICTING', 'UNKNOWN'],
  OrderDirection: ['ASC', 'DESC'],
  IssueOrderField: ['CREATED_AT', 'UPDATED_AT', 'COMMENTS'],
  RepositoryPermission: ['ADMIN', 'MAINTAIN', 'WRITE', 'TRIAGE', 'READ'],
};
function gqlErrorsFor(op: GqlOp): string[] {
  const errs: string[] = [];
  const checkFields = (fields: GqlField[], typeName: string): void => {
    const known = TYPE_FIELDS[typeName];
    for (const f of fields) {
      if (f.name === '__fragment') {
        if (f.inlineType) checkFields(f.children, f.inlineType);
        continue;
      }
      if (f.name === '__type' || f.name === '__typename') continue;
      if (known && !known.includes(f.name)) errs.push(`Cannot query field "${f.name}" on type "${typeName}".`);
      // Recurse with best-guess child type
      const childType = childTypeOf(typeName, f.name);
      if (childType) checkFields(f.children, childType);
    }
  };
  const rootType = op.kind === 'mutation' ? 'Mutation' : 'Query';
  for (const f of op.fields) {
    if (f.name === 'viewer') checkFields(f.children, 'User');
    else if (f.name === 'repository') checkFields(f.children, 'Repository');
    else if (f.name === 'node') checkFields(f.children, 'Node');
    else if (f.name === '__type') { /* introspection */ }
    else if (['createIssue', 'closeIssue', 'createPullRequest', 'mergePullRequest', 'addComment'].includes(f.name)) {
      // mutation payload types are permissive
      for (const c of f.children) {
        if (c.name === 'issue') checkFields(c.children, 'Issue');
        else if (c.name === 'pullRequest') checkFields(c.children, 'PullRequest');
        else if (c.name === 'commentEdge') checkFields(c.children, 'IssueCommentEdge');
      }
    } else if (rootType === 'Query') {
      errs.push(`Cannot query field "${f.name}" on type "Query".`);
    }
  }
  return errs;
}
function childTypeOf(parent: string, field: string): string | null {
  if (parent === 'Repository') {
    if (field === 'owner') return 'User';
    if (field === 'defaultBranchRef') return 'Ref';
    if (field === 'issue') return 'Issue';
    if (field === 'issues') return 'IssueConnection';
    if (field === 'pullRequests') return 'PullRequestConnection';
    if (field === 'pullRequest') return 'PullRequest';
  }
  if (parent === 'IssueConnection' || parent === 'PullRequestConnection') {
    if (field === 'nodes') return parent === 'IssueConnection' ? 'Issue' : 'PullRequest';
    if (field === 'pageInfo') return 'PageInfo';
  }
  if (parent === 'PullRequest' && field === 'files') return 'PullRequestChangedFileConnection';
  if (parent === 'PullRequestChangedFileConnection' && field === 'nodes') return 'PullRequestChangedFile';
  if (parent === 'Node') return null;
  return null;
}
function findRepoByGlobalId(id: string): Repo | null {
  const parsed = parseGlobalId(id);
  if (!parsed || parsed.kind !== 'Repository') return null;
  const dbId = Number(parsed.parts[0]);
  for (const r of reposByName.values()) if (r.id === dbId) return r;
  return null;
}
function resolveIssueNode(repo: Repo, issue: Issue, fields: GqlField[]): Record<string, unknown> {
  const out: Record<string, unknown> = {};
  for (const f of fields) {
    const key = f.alias ?? f.name;
    if (f.name === 'id') out[key] = globalId('Issue', repo.id, issue.number);
    else if (f.name === 'number') out[key] = issue.number;
    else if (f.name === 'title') out[key] = issue.title;
    else if (f.name === 'state') out[key] = issue.state.toUpperCase();
    else if (f.name === 'body') out[key] = issue.body;
    else if (f.name === 'url') out[key] = `https://example.invalid/${repoOwner(repo)}/${repo.name}/issues/${issue.number}`;
    else if (f.name === 'createdAt') out[key] = issue.createdAt;
    else if (f.name === 'updatedAt') out[key] = issue.updatedAt;
  }
  return out;
}
function prMergeable(repo: Repo, pr: Pull): string {
  if (pr.merged) return 'UNKNOWN';
  const m = squashMerge(repo, pr, branchTip(repo, pr.base));
  return m.conflict ? 'CONFLICTING' : 'MERGEABLE';
}
function resolvePrNode(repo: Repo, pr: Pull, fields: GqlField[]): Record<string, unknown> {
  const out: Record<string, unknown> = {};
  for (const f of fields) {
    const key = f.alias ?? f.name;
    if (f.name === 'id') out[key] = globalId('PullRequest', repo.id, pr.number);
    else if (f.name === 'number') out[key] = pr.number;
    else if (f.name === 'title') out[key] = pr.title;
    else if (f.name === 'state') out[key] = pr.merged ? 'MERGED' : pr.state.toUpperCase();
    else if (f.name === 'body') out[key] = pr.body;
    else if (f.name === 'headRefName') out[key] = pr.head;
    else if (f.name === 'baseRefName') out[key] = pr.base;
    else if (f.name === 'mergeable') out[key] = prMergeable(repo, pr);
    else if (f.name === 'merged') out[key] = pr.merged;
    else if (f.name === 'url') out[key] = `https://example.invalid/${repoOwner(repo)}/${repo.name}/pull/${pr.number}`;
    else if (f.name === 'createdAt') out[key] = isoNow();
    else if (f.name === 'files') {
      const first = typeof f.args.first === 'number' ? f.args.first : 100;
      const mbFiles = pr.mergeBase ? filesAt(repo, pr.mergeBase) : new Map<string, { oid: string; mode: string }>();
      const headFiles = filesAt(repo, pr.headSha);
      const diffs = diffFiles(mbFiles, headFiles).slice(0, first);
      out[key] = { nodes: diffs.map((d) => ({ path: d.path })), totalCount: diffs.length };
    }
  }
  return out;
}
function resolveRepoNode(repo: Repo, fields: GqlField[]): Record<string, unknown> {
  const out: Record<string, unknown> = {};
  const owner = repoOwner(repo);
  for (const f of fields) {
    const key = f.alias ?? f.name;
    if (f.name === 'id') out[key] = globalId('Repository', repo.id);
    else if (f.name === 'databaseId') out[key] = repo.id;
    else if (f.name === 'name') out[key] = repo.name;
    else if (f.name === 'nameWithOwner') out[key] = `${owner}/${repo.name}`;
    else if (f.name === 'owner') out[key] = { login: owner };
    else if (f.name === 'defaultBranchRef') out[key] = { name: repo.defaultBranch };
    else if (f.name === 'viewerPermission') out[key] = 'ADMIN';
    else if (f.name === 'hasIssuesEnabled') out[key] = true;
    else if (f.name === 'url') out[key] = `https://example.invalid/${owner}/${repo.name}`;
    else if (f.name === 'issue') {
      const num = f.args.number as number | undefined;
      const issue = typeof num === 'number' ? repo.issues.get(num) : undefined;
      out[key] = issue ? resolveIssueNode(repo, issue, f.children) : null;
    } else if (f.name === 'issues') {
      const first = typeof f.args.first === 'number' ? f.args.first : 100;
      const after = typeof f.args.after === 'string' ? f.args.after : null;
      const states = Array.isArray(f.args.states) ? (f.args.states as string[]) : null;
      const orderBy = (f.args.orderBy as Record<string, GqlValue> | undefined) ?? undefined;
      let list = [...repo.issues.values()];
      if (states) list = list.filter((i) => states.includes(i.state.toUpperCase()));
      const dir = orderBy?.direction === 'ASC' ? 1 : -1;
      list.sort((a, c) => (a.number - c.number) * dir);
      let startIdx = 0;
      if (after) {
        try {
          const n = Number(Buffer.from(after, 'base64').toString('utf8').split(':')[1]);
          const idx = list.findIndex((i) => i.number === n);
          if (idx >= 0) startIdx = idx + 1;
        } catch { /* ignore */ }
      }
      const page = list.slice(startIdx, startIdx + first);
      const hasNext = startIdx + first < list.length;
      const endCursor = page.length ? Buffer.from(`cursor:${page[page.length - 1]!.number}`).toString('base64') : null;
      const conn: Record<string, unknown> = {};
      for (const cf of f.children) {
        const ck = cf.alias ?? cf.name;
        if (cf.name === 'nodes') conn[ck] = page.map((i) => resolveIssueNode(repo, i, cf.children));
        else if (cf.name === 'pageInfo') conn[ck] = { hasNextPage: hasNext, endCursor };
        else if (cf.name === 'totalCount') conn[ck] = list.length;
      }
      out[key] = conn;
    } else if (f.name === 'pullRequests') {
      const first = typeof f.args.first === 'number' ? f.args.first : 100;
      const list = [...repo.pulls.values()].sort((a, c) => a.number - c.number).slice(0, first);
      const conn: Record<string, unknown> = {};
      for (const cf of f.children) {
        const ck = cf.alias ?? cf.name;
        if (cf.name === 'nodes') conn[ck] = list.map((p) => resolvePrNode(repo, p, cf.children));
        else if (cf.name === 'pageInfo') conn[ck] = { hasNextPage: false, endCursor: null };
        else if (cf.name === 'totalCount') conn[ck] = repo.pulls.size;
      }
      out[key] = conn;
    } else if (f.name === 'pullRequest') {
      const num = f.args.number as number | undefined;
      const pr = typeof num === 'number' ? repo.pulls.get(num) : undefined;
      out[key] = pr ? resolvePrNode(repo, pr, f.children) : null;
    }
  }
  return out;
}
function executeGql(op: GqlOp): { data: Record<string, unknown> | null; errors: Array<{ message: string }> } {
  const data: Record<string, unknown> = {};
  const errors: Array<{ message: string }> = [];
  const validation = gqlErrorsFor(op);
  if (validation.length) return { data: null, errors: validation.map((m) => ({ message: m })) };
  for (const f of op.fields) {
    const key = f.alias ?? f.name;
    if (op.kind === 'query') {
      if (f.name === 'viewer') {
        data[key] = { login: viewerLogin() };
        for (const c of f.children) { if (c.name !== 'login') data[key] = { login: viewerLogin() }; }
      } else if (f.name === 'repository') {
        const owner = String(f.args.owner ?? '');
        const name = String(f.args.name ?? '');
        const repo = lookupRepo(owner, name);
        data[key] = repo ? resolveRepoNode(repo, f.children) : null;
      } else if (f.name === 'node') {
        const id = String(f.args.id ?? '');
        const parsed = parseGlobalId(id);
        if (parsed?.kind === 'Repository') {
          const repo = findRepoByGlobalId(id);
          if (!repo) { data[key] = null; continue; }
          const node: Record<string, unknown> = { id };
          for (const c of f.children) {
            if (c.name === '__fragment') {
              if (c.inlineType === 'Repository') Object.assign(node, resolveRepoNode(repo, c.children));
              continue;
            }
            if (c.name === 'id') node[c.alias ?? 'id'] = id;
          }
          data[key] = node;
        } else if (parsed?.kind === 'Issue') {
          const repoId = Number(parsed.parts[0]); const num = Number(parsed.parts[1]);
          let found: { repo: Repo; issue: Issue } | null = null;
          for (const r of reposByName.values()) if (r.id === repoId && r.issues.has(num)) found = { repo: r, issue: r.issues.get(num)! };
          if (!found) { data[key] = null; continue; }
          const node: Record<string, unknown> = { id };
          for (const c of f.children) {
            if (c.name === '__fragment' && c.inlineType === 'Issue') Object.assign(node, resolveIssueNode(found.repo, found.issue, c.children));
          }
          data[key] = node;
        } else if (parsed?.kind === 'PullRequest') {
          const repoId = Number(parsed.parts[0]); const num = Number(parsed.parts[1]);
          let found: { repo: Repo; pr: Pull } | null = null;
          for (const r of reposByName.values()) if (r.id === repoId && r.pulls.has(num)) found = { repo: r, pr: r.pulls.get(num)! };
          if (!found) { data[key] = null; continue; }
          const node: Record<string, unknown> = { id };
          for (const c of f.children) {
            if (c.name === '__fragment' && c.inlineType === 'PullRequest') Object.assign(node, resolvePrNode(found.repo, found.pr, c.children));
          }
          data[key] = node;
        } else data[key] = null;
      } else if (f.name === '__type') {
        const typeName = String(f.args.name ?? '');
        const fields = TYPE_FIELDS[typeName] ?? [];
        const enums = TYPE_ENUMS[typeName] ?? [];
        const t: Record<string, unknown> = { name: typeName };
        for (const c of f.children) {
          const ck = c.alias ?? c.name;
          if (c.name === 'fields') t[ck] = fields.map((n) => ({ name: n }));
          else if (c.name === 'enumValues') t[ck] = enums.map((n) => ({ name: n }));
          else if (c.name === 'name') t[ck] = typeName;
          else if (c.name === 'kind') t[ck] = enums.length ? 'ENUM' : 'OBJECT';
        }
        data[key] = t;
      }
    } else {
      // mutations
      if (f.name === 'createIssue') {
        const input = (f.args.input ?? {}) as Record<string, GqlValue>;
        const repo = findRepoByGlobalId(String(input.repositoryId ?? ''));
        if (!repo) { errors.push({ message: 'repository not found' }); data[key] = { issue: null }; continue; }
        const number = repo.nextNumber++;
        const now = isoNow();
        const issue: Issue = { id: repo.id * 100000 + number, number, title: String(input.title ?? ''), body: String(input.body ?? ''), state: 'open', labels: [], user: repoOwner(repo), createdAt: now, updatedAt: now, seq: nextSeq() };
        repo.issues.set(number, issue);
        const payload: Record<string, unknown> = {};
        for (const c of f.children) if (c.name === 'issue') payload[c.alias ?? 'issue'] = resolveIssueNode(repo, issue, c.children);
        data[key] = payload;
      } else if (f.name === 'closeIssue') {
        const input = (f.args.input ?? {}) as Record<string, GqlValue>;
        const parsed = parseGlobalId(String(input.issueId ?? ''));
        let target: { repo: Repo; issue: Issue } | null = null;
        if (parsed?.kind === 'Issue') {
          const repoId = Number(parsed.parts[0]); const num = Number(parsed.parts[1]);
          for (const r of reposByName.values()) if (r.id === repoId && r.issues.has(num)) target = { repo: r, issue: r.issues.get(num)! };
        }
        if (!target) { errors.push({ message: 'issue not found' }); data[key] = { issue: null }; continue; }
        target.issue.state = 'closed';
        target.issue.updatedAt = isoNow();
        const payload: Record<string, unknown> = {};
        for (const c of f.children) if (c.name === 'issue') payload[c.alias ?? 'issue'] = resolveIssueNode(target.repo, target.issue, c.children);
        data[key] = payload;
      } else if (f.name === 'createPullRequest') {
        const input = (f.args.input ?? {}) as Record<string, GqlValue>;
        const repo = findRepoByGlobalId(String(input.repositoryId ?? ''));
        const headRef = String(input.headRefName ?? '');
        const baseRef = String(input.baseRefName ?? repo?.defaultBranch ?? 'main');
        if (!repo) { errors.push({ message: 'repository not found' }); data[key] = { pullRequest: null }; continue; }
        const headSha = branchTip(repo, headRef);
        const baseSha = branchTip(repo, baseRef);
        if (!headSha || !baseSha) { errors.push({ message: 'head or base branch not found' }); data[key] = { pullRequest: null }; continue; }
        const number = repo.nextNumber++;
        const pr: Pull = {
          id: repo.id * 100000 + number, number, title: String(input.title ?? ''), body: String(input.body ?? ''), state: 'open',
          head: headRef, base: baseRef, headSha, baseSha, mergeBase: mergeBaseOf(repo, headSha, baseSha),
          merged: false, mergedAt: null, mergeCommitSha: null, seq: nextSeq(),
        };
        repo.pulls.set(number, pr);
        const payload: Record<string, unknown> = {};
        for (const c of f.children) if (c.name === 'pullRequest') payload[c.alias ?? 'pullRequest'] = resolvePrNode(repo, pr, c.children);
        data[key] = payload;
      } else if (f.name === 'mergePullRequest') {
        const input = (f.args.input ?? {}) as Record<string, GqlValue>;
        const parsed = parseGlobalId(String(input.pullRequestId ?? ''));
        let target: { repo: Repo; pr: Pull } | null = null;
        if (parsed?.kind === 'PullRequest') {
          const repoId = Number(parsed.parts[0]); const num = Number(parsed.parts[1]);
          for (const r of reposByName.values()) if (r.id === repoId && r.pulls.has(num)) target = { repo: r, pr: r.pulls.get(num)! };
        }
        if (!target) { errors.push({ message: 'pull request not found' }); data[key] = { pullRequest: null }; continue; }
        const { repo, pr } = target;
        if (pr.state === 'open') {
          const merged = squashMerge(repo, pr, branchTip(repo, pr.base));
          if (!merged.conflict) {
            const tree = buildTreesFromFiles(repo.objects, merged.files);
            const baseTip = branchTip(repo, pr.base);
            const ts = EPOCH + nextSeq();
            const d = buildCommit(tree, baseTip ? [baseTip] : [], authorIdent(repo), `Merge pull request #${pr.number} from ${pr.head}`, ts);
            const mergeSha = putObj(repo.objects, 'commit', d);
            repo.refs.set(`refs/heads/${pr.base}`, mergeSha);
            touch(repo);
            pr.state = 'closed'; pr.merged = true; pr.mergedAt = isoNow(); pr.mergeCommitSha = mergeSha;
          }
        }
        const payload: Record<string, unknown> = {};
        for (const c of f.children) if (c.name === 'pullRequest') payload[c.alias ?? 'pullRequest'] = resolvePrNode(repo, pr, c.children);
        data[key] = payload;
      } else if (f.name === 'addComment') {
        const input = (f.args.input ?? {}) as Record<string, GqlValue>;
        const parsed = parseGlobalId(String(input.subjectId ?? ''));
        let target: { repo: Repo; issue: Issue } | null = null;
        if (parsed?.kind === 'Issue') {
          const repoId = Number(parsed.parts[0]); const num = Number(parsed.parts[1]);
          for (const r of reposByName.values()) if (r.id === repoId && r.issues.has(num)) target = { repo: r, issue: r.issues.get(num)! };
        }
        if (!target) { errors.push({ message: 'subject not found' }); data[key] = { commentEdge: null }; continue; }
        const comment: Comment = { id: target.repo.nextCommentId++, body: String(input.body ?? ''), user: repoOwner(target.repo), createdAt: isoNow() };
        const arr = target.repo.comments.get(target.issue.number) ?? [];
        arr.push(comment);
        target.repo.comments.set(target.issue.number, arr);
        const payload: Record<string, unknown> = {};
        for (const c of f.children) {
          if (c.name === 'commentEdge') {
            const node: Record<string, unknown> = {};
            for (const cc of c.children) {
              if (cc.name === 'node') {
                const n: Record<string, unknown> = {};
                for (const nfield of cc.children) {
                  if (nfield.name === 'id') n[nfield.alias ?? 'id'] = globalId('Comment', target.repo.id, target.issue.number, comment.id);
                  else if (nfield.name === 'body') n[nfield.alias ?? 'body'] = comment.body;
                }
                node[cc.alias ?? 'node'] = n;
              }
            }
            payload[c.alias ?? 'commentEdge'] = node;
          }
        }
        data[key] = payload;
      }
    }
  }
  return { data, errors };
}
async function handleGraphql(req: IncomingMessage, res: ServerResponse, rawBody: Buffer): Promise<void> {
  if (!authed(req)) { sendJson(res, 401, { message: 'Bad credentials' }); return; }
  let parsed: unknown;
  try { parsed = JSON.parse(rawBody.toString('utf8')); } catch { sendJson(res, 400, { message: 'Problems parsing JSON' }); return; }
  const ops = Array.isArray(parsed) ? parsed : [parsed];
  const results: unknown[] = [];
  for (const opBody of ops) {
    const rec = (opBody !== null && typeof opBody === 'object' ? opBody as Record<string, unknown> : {});
    const query = typeof rec.query === 'string' ? rec.query : '';
    const vars = (rec.variables !== null && typeof rec.variables === 'object' ? rec.variables as Record<string, unknown> : {});
    try {
      const parser = new GqlParser(query);
      const op = parser.parseOperation(vars);
      const result = executeGql(op);
      results.push(result.errors.length ? { data: result.data, errors: result.errors } : { data: result.data });
    } catch (err) {
      results.push({ data: null, errors: [{ message: err instanceof Error ? err.message : 'parse error' }] });
    }
  }
  sendJson(res, 200, Array.isArray(parsed) ? results : results[0]);
}

// ---------------------------------------------------------------- MCP
const MCP_TOOLS: Array<{ name: string; description: string; inputSchema: Record<string, unknown> }> = [
  {
    name: 'create_repo',
    description: 'Create a new repository owned by the authenticated user.',
    inputSchema: {
      type: 'object',
      properties: {
        name: { type: 'string', description: 'Repository name' },
        description: { type: 'string', description: 'Repository description' },
        private: { type: 'boolean', description: 'Whether the repository is private' },
        owner: { type: 'string', description: 'Owner login (defaults to the authenticated user)' },
      },
      required: ['name'],
    },
  },
  {
    name: 'get_repo',
    description: 'Get a repository by owner and name.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'Repository owner login' },
        repo: { type: 'string', description: 'Repository name' },
        full_name: { type: 'string', description: 'owner/repo' },
      },
      required: ['owner', 'repo'],
    },
  },
  {
    name: 'create_issue',
    description: 'Create an issue in a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'Repository owner login' },
        repo: { type: 'string', description: 'Repository name' },
        title: { type: 'string', description: 'Issue title' },
        body: { type: 'string', description: 'Issue body' },
        full_name: { type: 'string', description: 'owner/repo' },
      },
      required: ['owner', 'repo', 'title'],
    },
  },
  {
    name: 'list_issues',
    description: 'List issues in a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'Repository owner login' },
        repo: { type: 'string', description: 'Repository name' },
        state: { type: 'string', description: 'Issue state: open, closed or all' },
        full_name: { type: 'string', description: 'owner/repo' },
      },
      required: ['owner', 'repo'],
    },
  },
  {
    name: 'create_pull_request',
    description: 'Create a pull request in a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'Repository owner login' },
        repo: { type: 'string', description: 'Repository name' },
        title: { type: 'string', description: 'Pull request title' },
        body: { type: 'string', description: 'Pull request body' },
        head: { type: 'string', description: 'Head branch name' },
        base: { type: 'string', description: 'Base branch name' },
        full_name: { type: 'string', description: 'owner/repo' },
      },
      required: ['owner', 'repo', 'title', 'head', 'base'],
    },
  },
  {
    name: 'merge_pull_request',
    description: 'Merge a pull request in a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'Repository owner login' },
        repo: { type: 'string', description: 'Repository name' },
        pull_number: { type: 'integer', description: 'Pull request number' },
        full_name: { type: 'string', description: 'owner/repo' },
      },
      required: ['owner', 'repo', 'pull_number'],
    },
  },
];
function mcpResolveOwnerRepo(args: Record<string, unknown>): { owner: string; repo: string } | null {
  let owner = typeof args.owner === 'string' ? args.owner : (typeof args.owner_login === 'string' ? args.owner_login : '');
  let repo = typeof args.repo === 'string' ? args.repo : (typeof args.repository === 'string' ? args.repository : '');
  const full = typeof args.full_name === 'string' ? args.full_name : '';
  if ((!owner || !repo) && full.includes('/')) {
    const [o, r] = full.split('/', 2);
    if (!owner) owner = o ?? '';
    if (!repo) repo = r ?? '';
  }
  if (!owner) owner = viewerLogin();
  if (!repo) return null;
  return { owner, repo };
}
function mcpToolResult(obj: unknown): Record<string, unknown> {
  return { content: [{ type: 'text', text: JSON.stringify(obj) }], structuredContent: obj, isError: false };
}
function mcpToolError(message: string): Record<string, unknown> {
  return { content: [{ type: 'text', text: message }], isError: true };
}
function mcpCallTool(name: string, args: Record<string, unknown>): { result: Record<string, unknown> } | { error: { code: number; message: string } } {
  const tool = MCP_TOOLS.find((t) => t.name === name);
  if (!tool) return { error: { code: -32601, message: `unknown tool: ${name}` } };
  const required = (tool.inputSchema.required as string[] | undefined) ?? [];
  // Map common synonyms the suite may use onto canonical properties.
  const syn: Record<string, string[]> = {
    owner: ['owner', 'owner_login', 'login'], repo: ['repo', 'repository', 'repository_name', 'repo_name'],
    title: ['title'], body: ['body', 'description'], head: ['head', 'head_ref', 'head_branch'],
    base: ['base', 'base_ref', 'base_branch'], pull_number: ['pull_number', 'pull_request_number', 'pr_number', 'number'],
    name: ['name', 'repo', 'repository'], description: ['description', 'body'], private: ['private', 'is_private'],
    state: ['state', 'status'], full_name: ['full_name'],
  };
  const norm: Record<string, unknown> = {};
  for (const [canon, alts] of Object.entries(syn)) {
    for (const a of alts) if (args[a] !== undefined) { norm[canon] = args[a]; break; }
  }
  for (const r of required) {
    if (norm[r] === undefined || norm[r] === '' || norm[r] === null) {
      return { error: { code: -32602, message: `missing required argument: ${r}` } };
    }
  }
  try {
    if (name === 'create_repo') {
      const repoName = String(norm.name);
      const repo = createRepo(repoName, norm.private === true, typeof norm.description === 'string' ? norm.description : '');
      if (!repo) return { result: mcpToolError(`Repository already exists: ${repoName}`) };
      return { result: mcpToolResult({ ...repoJson(repo), full_name: `${repoOwner(repo)}/${repo.name}` }) };
    }
    const or = mcpResolveOwnerRepo({ ...args, ...norm });
    if (!or) return { error: { code: -32602, message: 'missing required argument: repo' } };
    const repo = lookupRepo(or.owner, or.repo);
    if (name === 'get_repo') {
      if (!repo) return { result: mcpToolError(`Repository not found: ${or.owner}/${or.repo}`) };
      return { result: mcpToolResult({ ...repoJson(repo), full_name: `${repoOwner(repo)}/${repo.name}` }) };
    }
    if (!repo) return { result: mcpToolError(`Repository not found: ${or.owner}/${or.repo}`) };
    if (name === 'create_issue') {
      const number = repo.nextNumber++;
      const now = isoNow();
      const issue: Issue = {
        id: repo.id * 100000 + number, number, title: String(norm.title ?? ''), body: typeof norm.body === 'string' ? norm.body : '',
        state: 'open', labels: [], user: repoOwner(repo), createdAt: now, updatedAt: now, seq: nextSeq(),
      };
      repo.issues.set(number, issue);
      return { result: mcpToolResult(issueJson(repo, issue)) };
    }
    if (name === 'list_issues') {
      const state = typeof norm.state === 'string' ? norm.state : 'open';
      let list = [...repo.issues.values()];
      if (state !== 'all') list = list.filter((i) => i.state === state);
      list.sort((a, c) => a.number - c.number);
      return { result: mcpToolResult(list.map((i) => issueJson(repo, i))) };
    }
    if (name === 'create_pull_request') {
      const headRef = String(norm.head).split(':').pop() ?? '';
      const baseRef = String(norm.base).split(':').pop() ?? repo.defaultBranch;
      const headSha = branchTip(repo, headRef);
      const baseSha = branchTip(repo, baseRef);
      if (!headSha || !baseSha) return { result: mcpToolError('head or base branch not found') };
      const existing = [...repo.pulls.values()].find((p) => p.head === headRef && p.base === baseRef && p.state === 'open');
      if (existing) return { result: mcpToolError('A pull request already exists') };
      const number = repo.nextNumber++;
      const pr: Pull = {
        id: repo.id * 100000 + number, number, title: String(norm.title ?? ''), body: typeof norm.body === 'string' ? norm.body : '',
        state: 'open', head: headRef, base: baseRef, headSha, baseSha, mergeBase: mergeBaseOf(repo, headSha, baseSha),
        merged: false, mergedAt: null, mergeCommitSha: null, seq: nextSeq(),
      };
      repo.pulls.set(number, pr);
      return { result: mcpToolResult(pullJson(repo, pr)) };
    }
    if (name === 'merge_pull_request') {
      const number = Number(norm.pull_number);
      const pr = repo.pulls.get(number);
      if (!pr) return { result: mcpToolError(`Pull request not found: ${number}`) };
      if (pr.state === 'closed') return { result: mcpToolError('Pull request is already closed') };
      const merged = squashMerge(repo, pr, branchTip(repo, pr.base));
      if (merged.conflict) return { result: mcpToolError('Merge conflict') };
      const tree = buildTreesFromFiles(repo.objects, merged.files);
      const baseTip = branchTip(repo, pr.base);
      const ts = EPOCH + nextSeq();
      const d = buildCommit(tree, baseTip ? [baseTip] : [], authorIdent(repo), `Merge pull request #${pr.number} from ${pr.head}`, ts);
      const mergeSha = putObj(repo.objects, 'commit', d);
      repo.refs.set(`refs/heads/${pr.base}`, mergeSha);
      touch(repo);
      pr.state = 'closed'; pr.merged = true; pr.mergedAt = isoNow(); pr.mergeCommitSha = mergeSha;
      return { result: mcpToolResult({ ...pullJson(repo, pr), sha: mergeSha, merged: true }) };
    }
    return { error: { code: -32601, message: `unknown tool: ${name}` } };
  } catch (err) {
    return { result: mcpToolError(err instanceof Error ? err.message : 'tool failed') };
  }
}
async function handleMcp(req: IncomingMessage, res: ServerResponse, rawBody: Buffer): Promise<void> {
  if (req.method === 'DELETE') { sendJson(res, 204, null); return; }
  if (req.method === 'GET') { sendJson(res, 405, { message: 'Method Not Allowed' }); return; }
  if (!authed(req)) {
    sendJson(res, 401, { jsonrpc: '2.0', id: null, error: { code: -32001, message: 'Unauthorized' } });
    return;
  }
  const text = rawBody.toString('utf8');
  let parsed: unknown;
  try { parsed = JSON.parse(text); } catch {
    const idMatch = /"id"\s*:\s*("[^"]*"|\d+)/.exec(text);
    const id: string | number | null = idMatch ? (idMatch[1]!.startsWith('"') ? JSON.parse(idMatch[1]!) as string : Number(idMatch[1])) : null;
    sendJson(res, 400, { jsonrpc: '2.0', id, error: { code: -32700, message: 'Parse error' } });
    return;
  }
  if (parsed === null || typeof parsed !== 'object' || Array.isArray(parsed)) {
    sendJson(res, 400, { jsonrpc: '2.0', id: null, error: { code: -32700, message: 'Parse error' } });
    return;
  }
  const msg = parsed as Record<string, unknown>;
  const id = (msg.id ?? null) as string | number | null;
  const method = typeof msg.method === 'string' ? msg.method : '';
  const params = (msg.params !== null && typeof msg.params === 'object' ? msg.params as Record<string, unknown> : {});
  const reply = (result: unknown): void => {
    sendJson(res, 200, { jsonrpc: '2.0', id, result });
  };
  const replyError = (code: number, message: string): void => {
    sendJson(res, 200, { jsonrpc: '2.0', id, error: { code, message } });
  };
  if (method === '' && id === null) { sendJson(res, 202, {}); return; }
  if (method.startsWith('notifications/')) { sendJson(res, 202, {}); return; }
  if (method === 'server/discover') {
    reply({
      supportedVersions: ['2026-07-28', '2025-11-25', '2025-06-18', '2025-03-26', '2024-11-05'],
      capabilities: { tools: {} },
      serverInfo: { name: 'github-core-clone', version: '1.0.0' },
      instructions: 'A GitHub-compatible git forge over MCP.',
      _meta: {
        'io.modelcontextprotocol/serverInfo': { name: 'github-core-clone', version: '1.0.0' },
        'io.modelcontextprotocol/protocolVersion': '2026-07-28',
      },
    });
    return;
  }
  if (method === 'initialize') {
    const requested = typeof params.protocolVersion === 'string' ? params.protocolVersion : '2025-11-25';
    const supported = ['2026-07-28', '2025-11-25', '2025-06-18', '2025-03-26', '2024-11-05'];
    reply({
      protocolVersion: supported.includes(requested) ? requested : '2025-11-25',
      capabilities: { tools: {} },
      serverInfo: { name: 'github-core-clone', version: '1.0.0' },
    });
    return;
  }
  if (method === 'ping') { reply({}); return; }
  if (method === 'tools/list') {
    reply({ tools: MCP_TOOLS });
    return;
  }
  if (method === 'tools/call') {
    const toolName = typeof params.name === 'string' ? params.name : '';
    const args = (params.arguments !== null && typeof params.arguments === 'object' ? params.arguments as Record<string, unknown> : {});
    const outcome = mcpCallTool(toolName, args);
    if ('error' in outcome) { replyError(outcome.error.code, outcome.error.message); return; }
    reply(outcome.result);
    return;
  }
  replyError(-32601, `Method not found: ${method}`);
}

// ---------------------------------------------------------------- server
export function createApp(): Server {
  return createServer(async (req: IncomingMessage, res: ServerResponse) => {
    const path = pathOf(req);
    const method = req.method ?? 'GET';
    try {
      if (method === 'GET' && path === '/healthz') { sendJson(res, 200, { ok: true }); return; }
      const rawBody = (method === 'POST' || method === 'PUT' || method === 'PATCH' || method === 'DELETE')
        ? await readBody(req) : Buffer.alloc(0);
      if (path === '/mcp' || path === '/mcp/') { await handleMcp(req, res, rawBody); return; }
      if (path === '/api/graphql') {
        if (method !== 'POST') { errJson(res, 404, 'Not Found'); return; }
        await handleGraphql(req, res, rawBody);
        return;
      }
      if (path.startsWith('/api/v3')) { await handleRest(req, res, path, method, rawBody); return; }
      // git smart HTTP (no auth required)
      if (/^\/[^/]+\/[^/]+\.git(\/.*)?$/.test(path)) {
        const handled = await handleGit(req, res, path, method, rawBody);
        if (handled) return;
      }
      errJson(res, 404, 'Not Found');
    } catch (err) {
      try { errJson(res, 500, err instanceof Error ? err.message : 'Internal Server Error'); } catch { /* socket gone */ }
    }
  });
}
