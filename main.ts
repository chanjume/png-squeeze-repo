// png-squeeze: lossless PNG re-encoder.
// Reads 1280x720 RGBA screenshots from MAKEFUN_INPUT_DIR/<id>/image.png and
// writes a smaller lossless PNG to MAKEFUN_OUTPUT_DIR/<id>/image.png.
// Node 22 built-ins only. Fully deterministic: no clock, no randomness.
// Strategy: decode to RGBA, try palette / grey / RGB(A) forms with several
// per-row filter choices, screen by zlib level 6, then re-deflate the best
// two candidates at level 9.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { deflateSync, inflateSync, constants as zlibConstants } from 'node:zlib';

// ---------------------------------------------------------------- CRC32
const CRC_TABLE: Uint32Array = (() => {
  const t = new Uint32Array(256);
  for (let n = 0; n < 256; n++) {
    let c = n;
    for (let k = 0; k < 8; k++) c = (c & 1) ? (0xedb88320 ^ (c >>> 1)) : (c >>> 1);
    t[n] = c >>> 0;
  }
  return t;
})();

function crc32(buf: Uint8Array, off: number, len: number): number {
  let c = 0xffffffff;
  for (let i = off; i < off + len; i++) c = CRC_TABLE[(c ^ buf[i]) & 0xff] ^ (c >>> 8);
  return (c ^ 0xffffffff) >>> 0;
}

function chunk(type: string, data: Uint8Array): Uint8Array {
  const out = new Uint8Array(12 + data.length);
  const dv = new DataView(out.buffer);
  dv.setUint32(0, data.length);
  for (let i = 0; i < 4; i++) out[4 + i] = type.charCodeAt(i);
  out.set(data, 8);
  dv.setUint32(8 + data.length, crc32(out, 4, 4 + data.length));
  return out;
}

function concat(parts: Uint8Array[]): Uint8Array {
  let total = 0;
  for (const p of parts) total += p.length;
  const out = new Uint8Array(total);
  let o = 0;
  for (const p of parts) { out.set(p, o); o += p.length; }
  return out;
}

// ---------------------------------------------------------------- decode
type Decoded = { width: number; height: number; rgba: Uint8Array };

function paeth(a: number, b: number, c: number): number {
  const p = a + b - c;
  const pa = Math.abs(p - a), pb = Math.abs(p - b), pc = Math.abs(p - c);
  if (pa <= pb && pa <= pc) return a;
  if (pb <= pc) return b;
  return c;
}

function decodePng(bytes: Uint8Array): Decoded {
  if (bytes.length < 8 || bytes[0] !== 137 || bytes[1] !== 80 || bytes[2] !== 78 || bytes[3] !== 71) {
    throw new Error('not a PNG');
  }
  let width = 0, height = 0, bitDepth = 0, colourType = 0, interlace = 0;
  let plte: Uint8Array | null = null;
  let trns: Uint8Array | null = null;
  const idatParts: Uint8Array[] = [];
  let off = 8;
  while (off + 8 <= bytes.length) {
    const len = (bytes[off] << 24) | (bytes[off + 1] << 16) | (bytes[off + 2] << 8) | bytes[off + 3];
    const type = String.fromCharCode(bytes[off + 4], bytes[off + 5], bytes[off + 6], bytes[off + 7]);
    const data = bytes.subarray(off + 8, off + 8 + len);
    if (type === 'IHDR') {
      width = (data[0] << 24) | (data[1] << 16) | (data[2] << 8) | data[3];
      height = (data[4] << 24) | (data[5] << 16) | (data[6] << 8) | data[7];
      bitDepth = data[8];
      colourType = data[9];
      interlace = data[12];
    } else if (type === 'PLTE') {
      plte = data.slice();
    } else if (type === 'tRNS') {
      trns = data.slice();
    } else if (type === 'IDAT') {
      idatParts.push(data);
    } else if (type === 'IEND') {
      break;
    }
    off += 12 + len;
  }
  if (bitDepth !== 8) throw new Error('unsupported bit depth ' + bitDepth);
  if (interlace !== 0) throw new Error('interlaced PNG unsupported');
  const bpp = colourType === 0 || colourType === 3 ? 1 : colourType === 4 ? 2 : colourType === 2 ? 3 : 4;
  const stride = width * bpp;
  const raw = inflateSync(concat(idatParts));
  if (raw.length !== height * (stride + 1)) throw new Error('bad inflated size');
  // Unfilter in place into a second buffer.
  const img = new Uint8Array(height * stride);
  for (let y = 0; y < height; y++) {
    const f = raw[y * (stride + 1)];
    const src = y * (stride + 1) + 1;
    const dst = y * stride;
    const prev = y > 0 ? img.subarray((y - 1) * stride, y * stride) : null;
    for (let x = 0; x < stride; x++) {
      const v = raw[src + x];
      const left = x >= bpp ? img[dst + x - bpp] : 0;
      const up = prev ? prev[x] : 0;
      const upLeft = prev && x >= bpp ? prev[x - bpp] : 0;
      let recon: number;
      if (f === 0) recon = v;
      else if (f === 1) recon = (v + left) & 255;
      else if (f === 2) recon = (v + up) & 255;
      else if (f === 3) recon = (v + ((left + up) >> 1)) & 255;
      else recon = (v + paeth(left, up, upLeft)) & 255;
      img[dst + x] = recon;
    }
  }
  // Convert to RGBA, preserving the RGB of fully transparent pixels.
  const rgba = new Uint8Array(width * height * 4);
  if (colourType === 6) {
    rgba.set(img);
  } else if (colourType === 2) {
    const kR = trns && trns.length >= 6 ? ((trns[0] << 8) | trns[1]) : -1;
    const kG = trns && trns.length >= 6 ? ((trns[2] << 8) | trns[3]) : -1;
    const kB = trns && trns.length >= 6 ? ((trns[4] << 8) | trns[5]) : -1;
    for (let i = 0, j = 0; i < img.length; i += 3, j += 4) {
      const r = img[i], g = img[i + 1], b = img[i + 2];
      rgba[j] = r; rgba[j + 1] = g; rgba[j + 2] = b;
      rgba[j + 3] = (kR >= 0 && r * 257 === kR && g * 257 === kG && b * 257 === kB) ? 0 : 255;
    }
  } else if (colourType === 0) {
    const k = trns && trns.length >= 2 ? ((trns[0] << 8) | trns[1]) : -1;
    for (let i = 0, j = 0; i < img.length; i++, j += 4) {
      const v = img[i];
      rgba[j] = v; rgba[j + 1] = v; rgba[j + 2] = v;
      rgba[j + 3] = (k >= 0 && v * 257 === k) ? 0 : 255;
    }
  } else if (colourType === 4) {
    for (let i = 0, j = 0; i < img.length; i += 2, j += 4) {
      const v = img[i];
      rgba[j] = v; rgba[j + 1] = v; rgba[j + 2] = v; rgba[j + 3] = img[i + 1];
    }
  } else if (colourType === 3) {
    if (!plte) throw new Error('palette PNG without PLTE');
    for (let i = 0, j = 0; i < img.length; i++, j += 4) {
      const idx = img[i] * 3;
      rgba[j] = plte[idx]; rgba[j + 1] = plte[idx + 1]; rgba[j + 2] = plte[idx + 2];
      rgba[j + 3] = trns && img[i] < trns.length ? trns[img[i]] : 255;
    }
  } else {
    throw new Error('unsupported colour type ' + colourType);
  }
  return { width, height, rgba };
}

// ---------------------------------------------------------------- filters
function filterRow(dst: Uint8Array, dstOff: number, row: Uint8Array, prev: Uint8Array | null, bpp: number, f: number): void {
  const n = row.length;
  dst[dstOff] = f;
  if (f === 0) { dst.set(row, dstOff + 1); return; }
  for (let i = 0; i < n; i++) {
    const v = row[i];
    const left = i >= bpp ? row[i - bpp] : 0;
    const up = prev ? prev[i] : 0;
    const upLeft = prev && i >= bpp ? prev[i - bpp] : 0;
    let p = 0;
    if (f === 1) p = left;
    else if (f === 2) p = up;
    else if (f === 3) p = (left + up) >> 1;
    else p = paeth(left, up, upLeft);
    dst[dstOff + 1 + i] = (v - p) & 255;
  }
}

// Signed-absolute sum of a filtered row (filter byte included).
function signedAbsSum(buf: Uint8Array, off: number, len: number): number {
  let s = 0;
  for (let i = off; i < off + len; i++) {
    const v = buf[i];
    s += v < 128 ? v : 256 - v;
  }
  return s;
}

const pairStamp = new Uint32Array(65536);
let pairGen = 0;

function pairCount(buf: Uint8Array, off: number, len: number): number {
  pairGen++;
  if (pairGen === 0xffffffff) { pairStamp.fill(0); pairGen = 1; }
  let count = 0;
  const end = off + len - 1;
  for (let i = off; i < end; i++) {
    const key = (buf[i] << 8) | buf[i + 1];
    if (pairStamp[key] !== pairGen) { pairStamp[key] = pairGen; count++; }
  }
  return count;
}

type FilterChoice = 0 | 1 | 2 | 4 | 'minsum' | 'pairs' | 'brute';

// Filter a whole form's samples according to a choice.
function filterImage(samples: Uint8Array, width: number, height: number, bpp: number, choice: FilterChoice): Uint8Array {
  const stride = width * bpp;
  const out = new Uint8Array(height * (stride + 1));
  const tmp = new Uint8Array(stride + 1);
  if (choice === 0 || choice === 1 || choice === 2 || choice === 4) {
    for (let y = 0; y < height; y++) {
      const row = samples.subarray(y * stride, (y + 1) * stride);
      const prev = y > 0 ? samples.subarray((y - 1) * stride, y * stride) : null;
      filterRow(out, y * (stride + 1), row, prev, bpp, choice);
    }
    return out;
  }
  if (choice === 'minsum') {
    // Pass 1: per-row winner by signed-abs sum over all 5 filters.
    const winners = new Uint8Array(height);
    for (let y = 0; y < height; y++) {
      const row = samples.subarray(y * stride, (y + 1) * stride);
      const prev = y > 0 ? samples.subarray((y - 1) * stride, y * stride) : null;
      let best = 0, bestSum = Infinity;
      for (let f = 0; f <= 4; f++) {
        filterRow(tmp, 0, row, prev, bpp, f);
        const s = signedAbsSum(tmp, 0, stride + 1);
        if (s < bestSum) { bestSum = s; best = f; }
      }
      winners[y] = best;
    }
    // Pass 2: write with the winners.
    for (let y = 0; y < height; y++) {
      const row = samples.subarray(y * stride, (y + 1) * stride);
      const prev = y > 0 ? samples.subarray((y - 1) * stride, y * stride) : null;
      filterRow(out, y * (stride + 1), row, prev, bpp, winners[y]);
    }
    return out;
  }
  if (choice === 'pairs') {
    for (let y = 0; y < height; y++) {
      const row = samples.subarray(y * stride, (y + 1) * stride);
      const prev = y > 0 ? samples.subarray((y - 1) * stride, y * stride) : null;
      let best = 0, bestCount = Infinity;
      for (let f = 0; f <= 4; f++) {
        filterRow(tmp, 0, row, prev, bpp, f);
        const c = pairCount(tmp, 0, stride + 1);
        if (c < bestCount) { bestCount = c; best = f; }
      }
      filterRow(out, y * (stride + 1), row, prev, bpp, best);
    }
    return out;
  }
  // 'brute': per row, deflate each filtered row at level 4 with the
  // previous 32768 filtered bytes as dictionary; keep the smallest.
  for (let y = 0; y < height; y++) {
    const row = samples.subarray(y * stride, (y + 1) * stride);
    const prev = y > 0 ? samples.subarray((y - 1) * stride, y * stride) : null;
    const pos = y * (stride + 1);
    let best = 0, bestLen = Infinity;
    for (let f = 0; f <= 4; f++) {
      filterRow(tmp, 0, row, prev, bpp, f);
      const dict = pos > 0 ? out.subarray(Math.max(0, pos - 32768), pos) : undefined;
      const comp = dict
        ? deflateSync(tmp, { level: 4, memLevel: 9, dictionary: dict })
        : deflateSync(tmp, { level: 4, memLevel: 9 });
      if (comp.length < bestLen) { bestLen = comp.length; best = f; }
    }
    filterRow(out, pos, row, prev, bpp, best);
  }
  return out;
}

// ---------------------------------------------------------------- forms
type Form = {
  colourType: number;
  bpp: number;
  samples: Uint8Array;
  plte: Uint8Array | null;
  trns: Uint8Array | null;
};

function pngSize(form: Form, idatLen: number): number {
  let s = 8 + 25 + 12 + idatLen + 12; // sig + IHDR + IDAT + IEND
  if (form.plte) s += 12 + form.plte.length;
  if (form.trns) s += 12 + form.trns.length;
  return s;
}

function buildForms(rgba: Uint8Array, width: number, height: number): Form[] {
  const n = width * height;
  let opaque = true;
  let grey = true;
  const counts = new Map<number, number>();
  let distinctCapped = false;
  for (let i = 0; i < n; i++) {
    const r = rgba[i * 4], g = rgba[i * 4 + 1], b = rgba[i * 4 + 2], a = rgba[i * 4 + 3];
    if (a !== 255) opaque = false;
    if (r !== g || g !== b) grey = false;
    if (!distinctCapped) {
      const w = ((r * 256 + g) * 256 + b) * 256 + a;
      counts.set(w, (counts.get(w) ?? 0) + 1);
      if (counts.size > 256) { distinctCapped = true; counts.clear(); }
    }
  }
  const forms: Form[] = [];

  // Transparent key: every non-opaque pixel fully transparent (alpha 0),
  // all sharing one colour value, and no opaque pixel carrying it.
  function greyKey(): number | null {
    if (!grey) return null;
    let key = -1;
    for (let i = 0; i < n; i++) {
      const a = rgba[i * 4 + 3];
      if (a !== 255) {
        if (a !== 0) return null;
        const v = rgba[i * 4];
        if (key < 0) key = v;
        else if (v !== key) return null;
      }
    }
    if (key < 0) return null;
    for (let i = 0; i < n; i++) {
      if (rgba[i * 4 + 3] === 255 && rgba[i * 4] === key) return null;
    }
    return key;
  }
  function rgbKey(): [number, number, number] | null {
    let kr = -1, kg = -1, kb = -1;
    for (let i = 0; i < n; i++) {
      const a = rgba[i * 4 + 3];
      if (a !== 255) {
        if (a !== 0) return null;
        const r = rgba[i * 4], g = rgba[i * 4 + 1], b = rgba[i * 4 + 2];
        if (kr < 0) { kr = r; kg = g; kb = b; }
        else if (r !== kr || g !== kg || b !== kb) return null;
      }
    }
    if (kr < 0) return null;
    for (let i = 0; i < n; i++) {
      if (rgba[i * 4 + 3] === 255 && rgba[i * 4] === kr && rgba[i * 4 + 1] === kg && rgba[i * 4 + 2] === kb) return null;
    }
    return [kr, kg, kb];
  }

  // Palette forms, when at most 256 distinct RGBA colours.
  if (!distinctCapped) {
    const entries: { w: number; count: number; r: number; g: number; b: number; a: number }[] = [];
    for (const [w, count] of counts) {
      const a = w & 255, b = (w >> 8) & 255, g = (w >> 16) & 255, r = (w >>> 24) & 255;
      entries.push({ w, count, r, g, b, a });
    }
    const lum = (e: { r: number; g: number; b: number }): number => 299 * e.r + 587 * e.g + 114 * e.b;
    const sortTransparentFirst = (
      arr: typeof entries,
      opaqueCmp: (x: (typeof entries)[number], y: (typeof entries)[number]) => number,
    ): typeof entries => {
      const trans = arr.filter((e) => e.a < 255);
      const opaq = arr.filter((e) => e.a === 255);
      trans.sort((x, y) => (x.a - y.a) || opaqueCmp(x, y));
      opaq.sort(opaqueCmp);
      return trans.concat(opaq);
    };
    const makePalette = (order: typeof entries): Form => {
      const plte = new Uint8Array(order.length * 3);
      const idxOf = new Map<number, number>();
      order.forEach((e, i) => {
        plte[i * 3] = e.r; plte[i * 3 + 1] = e.g; plte[i * 3 + 2] = e.b;
        idxOf.set(e.w, i);
      });
      let lastTrans = -1;
      order.forEach((e, i) => { if (e.a < 255) lastTrans = i; });
      const trns = lastTrans >= 0 ? new Uint8Array(order.slice(0, lastTrans + 1).map((e) => e.a)) : null;
      const samples = new Uint8Array(n);
      for (let i = 0; i < n; i++) {
        const w = ((rgba[i * 4] * 256 + rgba[i * 4 + 1]) * 256 + rgba[i * 4 + 2]) * 256 + rgba[i * 4 + 3];
        samples[i] = idxOf.get(w) as number;
      }
      return { colourType: 3, bpp: 1, samples, plte, trns };
    };
    // (a) count descending, word tie-break. Only filter 0 is tried for it.
    const orderA = sortTransparentFirst(entries.slice(), (x, y) => (y.count - x.count) || (x.w - y.w));
    const formA = makePalette(orderA);
    (formA as unknown as { onlyZero: boolean }).onlyZero = true;
    forms.push(formA);
    // (b) luminance ascending.
    const orderB = sortTransparentFirst(entries.slice(), (x, y) => (lum(x) - lum(y)) || (x.w - y.w));
    forms.push(makePalette(orderB));
  }

  if (grey) {
    const gk = greyKey();
    if (opaque || gk !== null) {
      const samples = new Uint8Array(n);
      for (let i = 0; i < n; i++) samples[i] = rgba[i * 4];
      const trns = gk !== null ? new Uint8Array([0, gk]) : null;
      forms.push({ colourType: 0, bpp: 1, samples, plte: null, trns });
    } else {
      const samples = new Uint8Array(n * 2);
      for (let i = 0; i < n; i++) { samples[i * 2] = rgba[i * 4]; samples[i * 2 + 1] = rgba[i * 4 + 3]; }
      forms.push({ colourType: 4, bpp: 2, samples, plte: null, trns: null });
    }
  } else {
    const rk = rgbKey();
    if (opaque || rk !== null) {
      const samples = new Uint8Array(n * 3);
      for (let i = 0; i < n; i++) {
        samples[i * 3] = rgba[i * 4]; samples[i * 3 + 1] = rgba[i * 4 + 1]; samples[i * 3 + 2] = rgba[i * 4 + 2];
      }
      const trns = rk !== null ? new Uint8Array([0, rk[0], 0, rk[1], 0, rk[2]]) : null;
      forms.push({ colourType: 2, bpp: 3, samples, plte: null, trns });
    } else {
      forms.push({ colourType: 6, bpp: 4, samples: rgba, plte: null, trns: null });
    }
  }
  return forms;
}

const ALL_CHOICES: FilterChoice[] = [0, 1, 2, 4, 'minsum', 'pairs', 'brute'];

function encodePng(form: Form, filtered: Uint8Array, idat: Uint8Array, width: number, height: number): Uint8Array {
  const ihdr = new Uint8Array(13);
  const dv = new DataView(ihdr.buffer);
  dv.setUint32(0, width);
  dv.setUint32(4, height);
  ihdr[8] = 8; // bit depth
  ihdr[9] = form.colourType;
  ihdr[10] = 0; // compression
  ihdr[11] = 0; // filter
  ihdr[12] = 0; // interlace
  const parts: Uint8Array[] = [
    new Uint8Array([137, 80, 78, 71, 13, 10, 26, 10]),
    chunk('IHDR', ihdr),
  ];
  if (form.plte) parts.push(chunk('PLTE', form.plte));
  if (form.trns) parts.push(chunk('tRNS', form.trns));
  parts.push(chunk('IDAT', idat));
  parts.push(chunk('IEND', new Uint8Array(0)));
  return concat(parts);
}

function processImage(rgba: Uint8Array, width: number, height: number): Uint8Array {
  const forms = buildForms(rgba, width, height);
  type Cand = { form: Form; choice: FilterChoice; filtered: Uint8Array; total: number };
  let best: Cand[] = [];
  for (const form of forms) {
    const onlyZero = (form as unknown as { onlyZero?: boolean }).onlyZero === true;
    const choices: FilterChoice[] = onlyZero ? [0] : ALL_CHOICES;
    for (const choice of choices) {
      const filtered = filterImage(form.samples, width, height, form.bpp, choice);
      const idat = deflateSync(filtered, { level: 6, memLevel: 8 });
      const total = pngSize(form, idat.length);
      best.push({ form, choice, filtered, total });
      best.sort((a, b) => a.total - b.total);
      if (best.length > 2) {
        best.length = 2; // drop the rest (their filtered buffers are freed)
      }
    }
  }
  // Final: candidate #1 tries 4 level-9 options, #2 tries 1.
  let bestOut: Uint8Array | null = null;
  let bestTotal = Infinity;
  const finals: { cand: Cand; level: number; memLevel: number; strategy: number }[] = [];
  if (best[0]) {
    for (const memLevel of [9, 8]) {
      for (const strategy of [zlibConstants.Z_DEFAULT_STRATEGY, zlibConstants.Z_FILTERED]) {
        finals.push({ cand: best[0], level: 9, memLevel, strategy });
      }
    }
  }
  if (best[1]) {
    finals.push({ cand: best[1], level: 9, memLevel: 9, strategy: zlibConstants.Z_DEFAULT_STRATEGY });
  }
  for (const f of finals) {
    const idat = deflateSync(f.cand.filtered, { level: f.level, memLevel: f.memLevel, strategy: f.strategy });
    const total = pngSize(f.cand.form, idat.length);
    if (total < bestTotal) {
      bestTotal = total;
      bestOut = encodePng(f.cand.form, f.cand.filtered, idat, width, height);
    }
  }
  if (!bestOut) throw new Error('no candidate produced');
  return bestOut;
}

// ---------------------------------------------------------------- main
const INPUT = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUTPUT = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

for (const id of readdirSync(INPUT).sort()) {
  const decoded = decodePng(new Uint8Array(readFileSync(join(INPUT, id, 'image.png'))));
  const out = processImage(decoded.rgba, decoded.width, decoded.height);
  mkdirSync(join(OUTPUT, id), { recursive: true });
  writeFileSync(join(OUTPUT, id, 'image.png'), out);
}
