/* Minimal QR encoder (byte mode, ECC level M, versions 1-6) — no CDN needed.
   window.SimpleQR.draw(canvas, text, {dark, light, margin}) */
(function () {
  var EXP = new Array(512), LOG = new Array(256);
  (function () {
    var x = 1;
    for (var i = 0; i < 255; i++) { EXP[i] = x; LOG[x] = i; x <<= 1; if (x & 0x100) x ^= 0x11d; }
    for (var j = 255; j < 512; j++) EXP[j] = EXP[j - 255];
  })();
  function mul(a, b) { return (a === 0 || b === 0) ? 0 : EXP[LOG[a] + LOG[b]]; }

  function genPoly(n) {
    var p = [1];
    for (var i = 0; i < n; i++) {
      var q = new Array(p.length + 1).fill(0);
      for (var j = 0; j < p.length; j++) { q[j] ^= p[j]; q[j + 1] ^= mul(p[j], EXP[i]); }
      p = q;
    }
    return p;
  }

  function ecBytes(data, n) {
    var g = genPoly(n), res = data.slice().concat(new Array(n).fill(0));
    for (var i = 0; i < data.length; i++) {
      var c = res[i]; if (c === 0) continue;
      for (var j = 0; j < g.length; j++) res[i + j] ^= mul(g[j], c);
    }
    return res.slice(data.length);
  }

  // version: [totalCodewords, ecPerBlock, [ [blocks, dataPerBlock], ... ] ]
  var VERSIONS = {
    1: [26, 10, [[1, 16]]],
    2: [44, 16, [[1, 28]]],
    3: [70, 26, [[1, 44]]],
    4: [100, 18, [[2, 32]]],
    5: [134, 24, [[2, 43]]],
    6: [172, 16, [[4, 27]]]
  };

  function pickVersion(len) {
    for (var v = 1; v <= 6; v++) {
      var cfg = VERSIONS[v], dataCw = 0;
      cfg[2].forEach(function (g) { dataCw += g[0] * g[1]; });
      if (dataCw - 2 >= len) return v; // 2 codewords for mode+count+terminator
    }
    return null;
  }

  function encodeData(text, version) {
    var bytes = [], i;
    var utf = unescape(encodeURIComponent(text));
    for (i = 0; i < utf.length; i++) bytes.push(utf.charCodeAt(i) & 0xff);
    var cfg = VERSIONS[version], dataCw = 0;
    cfg[2].forEach(function (g) { dataCw += g[0] * g[1]; });

    var bits = [];
    function push(val, n) { for (var k = n - 1; k >= 0; k--) bits.push((val >> k) & 1); }
    push(4, 4);              // byte mode
    push(bytes.length, 8);   // count (versions 1-9)
    for (i = 0; i < bytes.length; i++) push(bytes[i], 8);
    var cap = dataCw * 8;
    for (i = 0; i < 4 && bits.length < cap; i++) bits.push(0);
    while (bits.length % 8 !== 0) bits.push(0);
    var cw = [];
    for (i = 0; i < bits.length; i += 8) {
      var b = 0; for (var j = 0; j < 8; j++) b = (b << 1) | bits[i + j];
      cw.push(b);
    }
    var pad = [0xEC, 0x11], p = 0;
    while (cw.length < dataCw) { cw.push(pad[p++ % 2]); }

    // split into blocks
    var blocks = [], idx = 0;
    cfg[2].forEach(function (g) {
      for (var n = 0; n < g[0]; n++) { blocks.push(cw.slice(idx, idx + g[1])); idx += g[1]; }
    });
    var ecs = blocks.map(function (b) { return ecBytes(b, cfg[1]); });

    var out = [], maxD = Math.max.apply(null, blocks.map(function (b) { return b.length; }));
    for (i = 0; i < maxD; i++) blocks.forEach(function (b) { if (i < b.length) out.push(b[i]); });
    for (i = 0; i < cfg[1]; i++) ecs.forEach(function (e) { out.push(e[i]); });
    return out;
  }

  function buildMatrix(version, codewords) {
    var size = version * 4 + 17;
    var m = [], fn = [], r, c;
    for (r = 0; r < size; r++) { m.push(new Array(size).fill(0)); fn.push(new Array(size).fill(0)); }

    function setF(r0, c0, v) { m[r0][c0] = v; fn[r0][c0] = 1; }

    function finder(r0, c0) {
      for (r = -1; r <= 7; r++) for (c = -1; c <= 7; c++) {
        var rr = r0 + r, cc = c0 + c;
        if (rr < 0 || cc < 0 || rr >= size || cc >= size) continue;
        var inRing = (r >= 0 && r <= 6 && (c === 0 || c === 6)) || (c >= 0 && c <= 6 && (r === 0 || r === 6));
        var inCore = r >= 2 && r <= 4 && c >= 2 && c <= 4;
        setF(rr, cc, (inRing || inCore) ? 1 : 0);
      }
    }
    finder(0, 0); finder(0, size - 7); finder(size - 7, 0);

    for (c = 8; c < size - 8; c++) { setF(6, c, c % 2 === 0 ? 1 : 0); setF(c, 6, c % 2 === 0 ? 1 : 0); }

    if (version > 1) {
      var ac = size - 7;
      for (r = -2; r <= 2; r++) for (c = -2; c <= 2; c++) {
        var ring = Math.max(Math.abs(r), Math.abs(c));
        setF(ac + r, ac + c, (ring === 1) ? 0 : 1);
      }
    }

    setF(size - 8, 8, 1); // dark module

    // reserve format areas
    for (var i = 0; i < 9; i++) {
      if (!fn[8][i]) setF(8, i, 0);
      if (!fn[i][8]) setF(i, 8, 0);
    }
    for (i = 0; i < 8; i++) {
      if (!fn[8][size - 1 - i]) setF(8, size - 1 - i, 0);
      if (!fn[size - 1 - i][8]) setF(size - 1 - i, 8, 0);
    }

    // place data
    var bits = [];
    codewords.forEach(function (b) { for (var k = 7; k >= 0; k--) bits.push((b >> k) & 1); });
    var bi = 0, up = true;
    for (var col = size - 1; col > 0; col -= 2) {
      if (col === 6) col--;
      for (var n = 0; n < size; n++) {
        var row = up ? size - 1 - n : n;
        for (var d = 0; d < 2; d++) {
          var cc2 = col - d;
          if (fn[row][cc2]) continue;
          m[row][cc2] = bi < bits.length ? bits[bi] : 0;
          bi++;
        }
      }
      up = !up;
    }
    return { m: m, fn: fn, size: size };
  }

  function maskFn(k, r, c) {
    switch (k) {
      case 0: return (r + c) % 2 === 0;
      case 1: return r % 2 === 0;
      case 2: return c % 3 === 0;
      case 3: return (r + c) % 3 === 0;
      case 4: return (Math.floor(r / 2) + Math.floor(c / 3)) % 2 === 0;
      case 5: return ((r * c) % 2) + ((r * c) % 3) === 0;
      case 6: return (((r * c) % 2) + ((r * c) % 3)) % 2 === 0;
      case 7: return (((r + c) % 2) + ((r * c) % 3)) % 2 === 0;
    }
  }

  function penalty(m, size) {
    var p = 0, r, c, i, run, dark = 0;
    for (r = 0; r < size; r++) {
      run = 1;
      for (c = 1; c < size; c++) {
        if (m[r][c] === m[r][c - 1]) { run++; } else { if (run >= 5) p += 3 + (run - 5); run = 1; }
      }
      if (run >= 5) p += 3 + (run - 5);
    }
    for (c = 0; c < size; c++) {
      run = 1;
      for (r = 1; r < size; r++) {
        if (m[r][c] === m[r - 1][c]) { run++; } else { if (run >= 5) p += 3 + (run - 5); run = 1; }
      }
      if (run >= 5) p += 3 + (run - 5);
    }
    for (r = 0; r < size - 1; r++) for (c = 0; c < size - 1; c++) {
      var v = m[r][c];
      if (v === m[r][c + 1] && v === m[r + 1][c] && v === m[r + 1][c + 1]) p += 3;
    }
    var pat = [1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0];
    function match(get, len) {
      var cnt = 0;
      for (i = 0; i + 11 <= len; i++) {
        var ok = true, ok2 = true;
        for (var j = 0; j < 11; j++) {
          if (get(i + j) !== pat[j]) ok = false;
          if (get(i + j) !== pat[10 - j]) ok2 = false;
        }
        if (ok || ok2) cnt++;
      }
      return cnt * 40;
    }
    for (r = 0; r < size; r++) p += match(function (x) { return m[r][x]; }, size);
    for (c = 0; c < size; c++) p += match(function (x) { return m[x][c]; }, size);
    for (r = 0; r < size; r++) for (c = 0; c < size; c++) if (m[r][c]) dark++;
    var ratio = Math.abs((dark * 100) / (size * size) - 50);
    p += Math.floor(ratio / 5) * 10;
    return p;
  }

  function formatBits(mask) {
    var data = (0 << 3) | mask; // level M = 00
    var v = data << 10;
    var g = 0x537;
    for (var i = 4; i >= 0; i--) if (v & (1 << (i + 10))) v ^= g << i;
    return ((data << 10) | v) ^ 0x5412;
  }

  function placeFormat(m, size, mask) {
    var f = formatBits(mask);
    function bit(i) { return (f >> i) & 1; }
    for (var i = 0; i <= 5; i++) m[8][i] = bit(i);
    m[8][7] = bit(6); m[8][8] = bit(7); m[7][8] = bit(8);
    for (i = 9; i <= 14; i++) m[14 - i][8] = bit(i);
    for (i = 0; i <= 7; i++) m[size - 1 - i][8] = bit(i);
    for (i = 8; i <= 14; i++) m[8][size - 15 + i] = bit(i);
    m[size - 8][8] = 1;
  }

  function encode(text) {
    var utf = unescape(encodeURIComponent(text));
    var version = pickVersion(utf.length);
    if (!version) throw new Error('text too long for SimpleQR');
    var cw = encodeData(text, version);
    var base = buildMatrix(version, cw);
    var best = null;
    for (var k = 0; k < 8; k++) {
      var m = base.m.map(function (row) { return row.slice(); });
      for (var r = 0; r < base.size; r++) for (var c = 0; c < base.size; c++) {
        if (!base.fn[r][c] && maskFn(k, r, c)) m[r][c] ^= 1;
      }
      placeFormat(m, base.size, k);
      var p = penalty(m, base.size);
      if (!best || p < best.p) best = { m: m, p: p, k: k };
    }
    return { modules: best.m, size: base.size, version: version, mask: best.k };
  }

  function draw(canvas, text, opts) {
    opts = opts || {};
    var q = encode(text);
    var margin = opts.margin == null ? 2 : opts.margin;
    var total = q.size + margin * 2;
    var px = Math.max(1, Math.floor((canvas.width || 400) / total));
    var dim = px * total;
    canvas.width = dim; canvas.height = dim;
    var ctx = canvas.getContext('2d');
    ctx.fillStyle = opts.light || '#ffffff';
    ctx.fillRect(0, 0, dim, dim);
    ctx.fillStyle = opts.dark || '#000000';
    for (var r = 0; r < q.size; r++) for (var c = 0; c < q.size; c++) {
      if (q.modules[r][c]) ctx.fillRect((c + margin) * px, (r + margin) * px, px, px);
    }
    return q;
  }

  window.SimpleQR = { encode: encode, draw: draw };
})();
