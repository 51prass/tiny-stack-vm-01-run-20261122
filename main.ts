// Tiny stack VM: faithful interpreter of make.fun's tiny stack ISA (32-bit wrapping
// values, 256-value stack, 64-deep call stack, 256 words of memory, 1M steps,
// 64K output, ten traps with their own exit codes). Written from ISA.md + vm.mjs.
import { mkdirSync as k, readdirSync as d, readFileSync as f, writeFileSync as w } from 'node:fs';
import { join as j } from 'node:path';
const I = process.env.MAKEFUN_INPUT_DIR ?? '/input', O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const N = new Uint8Array(256), P = new Uint8Array(256), Q = new Uint8Array(256), V = new Uint8Array(256);
for (const [o, a, b, i = 0] of [[1, 0, 1, 1], [2, 0, 1, 4], [3, 1], [4, 1, 2], [5, 2, 2], [6, 2, 3], [7, 3, 3], [23, 1, 1], [27, 1, 1], [48, 0, 0, 2], [49, 1, 0, 2], [50, 1, 0, 2], [51, 0, 0, 2], [52], [64, 1, 1], [65, 2], [80, 1], [81, 1], [82, 0, 1], [83, 1]]) { V[o] = 1; N[o] = i; P[o] = a; Q[o] = b || 0; }
V[0] = 1;
for (let o = 16; o < 35; o++) if (o != 23 && o != 27) { V[o] = 1; P[o] = 2; Q[o] = 1; }
function r(p, q) {
  const D = new Int32Array(256), C = new Int32Array(64), Y = new Int32Array(256), u = [];
  let s = 0, t = 0, y = 0, c = 0, h = 0;
  const n = p.length;
  for (;;) {
    if (h == 1e6) return [u, 10];
    if (c < 0 || c >= n) return [u, 9];
    const o = p[c];
    if (!V[o]) return [u, 5];
    const m = N[o];
    if (c + m >= n) return [u, 9];
    h++;
    const x = c + 1 + m, g = P[o];
    if (s < g) return [u, 2];
    if (s - g + Q[o] > 256) return [u, 3];
    c = x;
    switch (o) {
      case 0: return [u, 0];
      case 1: D[s++] = (p[x - 1] << 24) >> 24; break;
      case 2: D[s++] = p[x - 4] | (p[x - 3] << 8) | (p[x - 2] << 16) | (p[x - 1] << 24); break;
      case 3: s--; break;
      case 4: D[s] = D[s - 1]; s++; break;
      case 5: { const v = D[s - 1]; D[s - 1] = D[s - 2]; D[s - 2] = v; break; }
      case 6: D[s] = D[s - 2]; s++; break;
      case 7: { const v = D[s - 3]; D[s - 3] = D[s - 2]; D[s - 2] = D[s - 1]; D[s - 1] = v; break; }
      case 23: D[s - 1] = -D[s - 1] | 0; break;
      case 27: D[s - 1] = ~D[s - 1]; break;
      case 48: case 49: case 50: {
        const e = ((p[x - 2] | (p[x - 1] << 8)) << 16) >> 16;
        let k = 1;
        if (o > 48) { const v = D[--s]; k = o == 49 ? v == 0 : v != 0; }
        if (k) c = x + e;
        break;
      }
      case 51:
        if (t == 64) return [u, 7];
        C[t++] = x; c = p[x - 2] | (p[x - 1] << 8);
        break;
      case 52:
        if (!t) return [u, 8];
        c = C[--t];
        break;
      case 64: {
        const v = D[s - 1];
        if (v < 0 || v > 255) return [u, 6];
        D[s - 1] = Y[v];
        break;
      }
      case 65: {
        const v = D[s - 1], z = D[s - 2];
        if (v < 0 || v > 255) return [u, 6];
        s -= 2; Y[v] = z;
        break;
      }
      case 80: {
        const v = String(D[s - 1]);
        if (u.length + v.length > 65536) return [u, 11];
        s--;
        for (let i = 0; i < v.length; i++) u.push(v.charCodeAt(i));
        break;
      }
      case 81:
        if (u.length >= 65536) return [u, 11];
        u.push(D[--s] & 255);
        break;
      case 82: D[s++] = y < q.length ? q[y++] : -1; break;
      case 83: return [u, D[--s] & 255];
      default: {
        const b = D[s - 1], a = D[s - 2];
        let v;
        if (o == 16) v = (a + b) | 0;
        else if (o == 17) v = (a - b) | 0;
        else if (o == 18) v = Math.imul(a, b);
        else if (o == 19) { if (!b) return [u, 4]; v = a == -2147483648 && b == -1 ? a : (a / b) | 0; }
        else if (o == 20) { if (!b) return [u, 4]; v = b == -1 ? 0 : a % b | 0; }
        else if (o == 21) { if (!b) return [u, 4]; v = Math.floor((a >>> 0) / (b >>> 0)) | 0; }
        else if (o == 22) { if (!b) return [u, 4]; v = (a >>> 0) % (b >>> 0) | 0; }
        else if (o == 24) v = a & b;
        else if (o == 25) v = a | b;
        else if (o == 26) v = a ^ b;
        else if (o == 28) v = a << (b & 31);
        else if (o == 29) v = a >> (b & 31);
        else if (o == 30) v = (a >>> (b & 31)) | 0;
        else if (o == 32) v = a == b ? 1 : 0;
        else if (o == 33) v = a < b ? 1 : 0;
        else v = (a >>> 0) < (b >>> 0) ? 1 : 0;
        s -= 2; D[s++] = v;
      }
    }
  }
}
for (const id of d(I).sort()) {
  const [u, v] = r(new Uint8Array(f(j(I, id, 'program.bin'))), new Uint8Array(f(j(I, id, 'input.bin'))));
  k(j(O, id), { recursive: !0 });
  w(j(O, id, 'stdout.bin'), Uint8Array.from(u));
  w(j(O, id, 'exit.txt'), v + '\n');
}
