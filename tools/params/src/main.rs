//! Parameter tables for "Randomized Symbolic FRI" (Chapter 7).
//!
//! Field: Goldilocks p = 2^64 - 2^32 + 1, challenge field K = F_{p^3}.
//! Message length L = 2^20, security target lambda = 128.
//!
//! Usage: cargo run --release -- <params.tex> <fs.tex>
//! Writes the interactive tables to <params.tex>, the Fiat-Shamir table to <fs.tex>,
//! and a plain summary to stdout.

use std::fmt::Write as _;
use std::fs;

const LAMBDA: f64 = 128.0;
const LOG2_L: u32 = 20;
/// Gap above the Johnson radius used in the provisional Johnson columns.
const ETA: f64 = 0.02;
/// Bytes per base-field element (layer-0 leaves) and per K-element (layers >= 1).
const BYTES_F: f64 = 8.0;
const BYTES_K: f64 = 24.0;
const BYTES_HASH: f64 = 32.0;

const P_GOLDILOCKS: f64 = 18446744069414584321.0; // 2^64 - 2^32 + 1

fn card_k() -> f64 {
    P_GOLDILOCKS.powi(3)
}

struct FsRow {
    rho_inv: u32,
    /// (extension degree e, log2 Q, commit-phase bits, s or None)
    cells: Vec<(u32, u32, f64, Option<u32>)>,
}

/// State-restoration unique binding (Theorem in the Fiat-Shamir chapter), binary arity:
/// Q (eps_cr + ((1+rho)/2)^s) + d/(|K|-1) <= 2^-lambda, eps_cr = (a_1-1) n_1 / |K|.
fn fs_row(rho_inv: u32) -> FsRow {
    let mut cells = Vec::new();
    for (e, log2_q) in [(3u32, 40u32), (3, 64), (4, 64)] {
        let kf = P_GOLDILOCKS.powi(e as i32);
        let q_count = 2f64.powi(log2_q as i32);
        let log2_n = LOG2_L + rho_inv.trailing_zeros();
        let n1 = 2f64.powi(log2_n as i32 - 1);
        let d = LOG2_L as f64;
        let eps_cr = n1 / kf;
        let commit_bits = -(q_count * eps_cr).log2();
        let target = 2f64.powf(-LAMBDA);
        let q = (1.0 + 1.0 / rho_inv as f64) / 2.0;
        let fixed = q_count * eps_cr + d / (kf - 1.0);
        let s = if fixed >= target {
            None
        } else {
            (1..100_000).find(|&s| fixed + q_count * q.powi(s as i32) <= target)
        };
        cells.push((e, log2_q, commit_bits, s));
    }
    FsRow { rho_inv, cells }
}

/// Smallest s >= 1 with `eps + q^s <= 2^-lambda`, or None if impossible.
fn s_upper(eps: f64, q: f64) -> Option<u32> {
    let target = 2f64.powf(-LAMBDA);
    if eps >= target || !(0.0..1.0).contains(&q) {
        return None;
    }
    (1..100_000).find(|&s| eps + q.powi(s as i32) <= target)
}

/// Smallest s >= 1 with `c * q^s - sub <= 2^-lambda` (attack no longer breaks the target).
fn s_attack(c: f64, q: f64, sub: f64) -> u32 {
    let target = 2f64.powf(-LAMBDA);
    (1..100_000)
        .find(|&s| c * q.powi(s as i32) - sub <= target)
        .expect("attack bound does not decay")
}

struct Row {
    rho_inv: u32,
    a: u32,
    k: u32,
    d: u32,
    log2_n: u32,
    log2_eps_ud: f64,
    s_a: u32,
    s_lo: u32,
    k_elems: f64,
    hashes: f64,
    proof_kib: f64,
}

fn unique_row(rho_inv: u32, log2_a: u32) -> Row {
    let kf = card_k();
    let a = 1u32 << log2_a;
    assert!(LOG2_L % log2_a == 0, "arity must divide the message length");
    let k = LOG2_L / log2_a;
    let d = k * (a - 1);
    let b = rho_inv as f64;
    let log2_n = LOG2_L + rho_inv.trailing_zeros();
    let n = 2f64.powi(log2_n as i32);
    let n1 = n / a as f64;
    let rho = 1.0 / b;

    // Theorem 5.2: (N-B)/|K| + d/(|K|-1) + ((1+rho)/2)^s.
    let eps_ud = (n - b) / kf;
    let eps_sz = d as f64 / (kf - 1.0);
    let q = (1.0 + rho) / 2.0;
    let s_a = s_upper(eps_ud + eps_sz, q).expect("unique-binding target unreachable");

    // Theorem 6.3: (1 - d/|K|) ((1+rho)/2 - 2/n_1)^s.
    let s_lo = s_attack(1.0 - d as f64 / kf, q - 2.0 / n1, 0.0);

    // Opened data per query path (W_k omitted, leaves grouped by fibre).
    // Layer i < k: one fibre of a leaves; layer 0 in F, layer i >= 1 has T-degree <= i(a-1).
    let mut k_elems = 0.0; // K-elements (layers >= 1)
    let mut f_elems = 0.0; // F-elements (layer 0)
    let mut hashes = 0.0;
    for i in 0..k {
        let coeffs = (i * (a - 1) + 1) as f64;
        if i == 0 {
            f_elems += a as f64;
        } else {
            k_elems += a as f64 * coeffs;
        }
        // Merkle tree over the n_{i+1} fibres of layer i.
        hashes += (log2_n - (i + 1) * log2_a) as f64;
    }
    let per_path = f_elems * BYTES_F + k_elems * BYTES_K + hashes * BYTES_HASH;
    let fixed = (d + 1) as f64 * BYTES_K + k as f64 * BYTES_HASH;
    let proof_kib = (s_a as f64 * per_path + fixed) / 1024.0;

    Row {
        rho_inv,
        a,
        k,
        d,
        log2_n,
        log2_eps_ud: eps_ud.log2(),
        s_a,
        s_lo,
        k_elems: k_elems + f_elems,
        hashes,
        proof_kib,
    }
}

struct JRow {
    rho_inv: u32,
    alpha: f64,
    ell: u32,
    s_j: u32,
    m: f64,
    s_e: u32,
    s_e_lo: u32,
}

fn johnson_row(rho_inv: u32) -> JRow {
    // Binary arity; d = 20. Provisional: eps^J_MCA is set to 0 here.
    let kf = card_k();
    let d = LOG2_L as f64;
    let rho = 1.0 / rho_inv as f64;
    let n1 = 2f64.powi((LOG2_L + rho_inv.trailing_zeros()) as i32) / 2.0;
    let alpha = rho.sqrt() + ETA;
    let ell = ((alpha - rho) / (alpha * alpha - rho)).floor() as u32;
    let ellf = ell as f64;
    let eps_sz = (ellf + ellf * (ellf - 1.0) / 2.0) * d / (kf - 1.0);
    let s_j = s_upper(eps_sz, alpha).expect("Johnson target unreachable");
    let q = (1.0 + rho) / 2.0;
    let m = alpha.max(q * q);
    let s_e = s_upper(2.0 * eps_sz, m).expect("equivocation target unreachable");
    // Theorem 6.7: ((1+rho)/2 - 1/n_1)^{2s} - 2 ell d/|K|.
    let qq = (q - 1.0 / n1) * (q - 1.0 / n1);
    let s_e_lo = s_attack(1.0, qq, 2.0 * ellf * d / kf);
    JRow { rho_inv, alpha, ell, s_j, m, s_e, s_e_lo }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    assert!(args.len() == 3, "usage: sfri-params <params.tex> <fs.tex>");
    let out = args[1].clone();
    let out_fs = args[2].clone();

    let mut rows = Vec::new();
    for rho_inv in [2u32, 4, 8, 16] {
        for log2_a in [1u32, 2, 4] {
            rows.push(unique_row(rho_inv, log2_a));
        }
    }
    let jrows: Vec<JRow> = [2u32, 4, 8, 16].into_iter().map(johnson_row).collect();

    let mut tex = String::new();
    writeln!(tex, "% Generated by tools/params (sfri-params). Do not edit by hand.").unwrap();
    writeln!(tex, "\\begin{{table}}[ht]\\centering\\small").unwrap();
    writeln!(tex, "\\renewcommand{{\\arraystretch}}{{1.15}}").unwrap();
    writeln!(tex, "\\begin{{tabular}}{{rrrrrrrrrrr}}").unwrap();
    writeln!(tex, "\\hline").unwrap();
    writeln!(tex, "$1/\\rho$ & $a$ & $k$ & $d$ & $\\log_2N$ & $\\log_2\\eps_{{\\mathrm{{UD}}}}$ & $s_A$ & $s_{{\\mathrm{{att}}}}$ & elts/path & hashes/path & proof (KiB)\\\\").unwrap();
    writeln!(tex, "\\hline").unwrap();
    for r in &rows {
        writeln!(
            tex,
            "{} & {} & {} & {} & {} & ${:.1}$ & {} & {} & {:.0} & {:.0} & {:.0}\\\\",
            r.rho_inv, r.a, r.k, r.d, r.log2_n, r.log2_eps_ud, r.s_a, r.s_lo, r.k_elems, r.hashes, r.proof_kib
        )
        .unwrap();
    }
    writeln!(tex, "\\hline\\end{{tabular}}").unwrap();
    writeln!(tex, "\\caption{{Unique binding at $\\lambda=128$, $L=2^{{20}}$, $\\K=\\F_{{p^3}}$ (Goldilocks). $s_A$: smallest $s$ satisfying \\cref{{thm:unique-binding}}; $s_{{\\mathrm{{att}}}}$: smallest $s$ not broken by \\cref{{thm:ub-tight}}.}}").unwrap();
    writeln!(tex, "\\label{{tab:unique}}").unwrap();
    writeln!(tex, "\\end{{table}}").unwrap();
    writeln!(tex).unwrap();
    writeln!(tex, "\\begin{{table}}[ht]\\centering\\small").unwrap();
    writeln!(tex, "\\renewcommand{{\\arraystretch}}{{1.15}}").unwrap();
    writeln!(tex, "\\begin{{tabular}}{{rrrrrrr}}").unwrap();
    writeln!(tex, "\\hline").unwrap();
    writeln!(tex, "$1/\\rho$ & $\\alpha=\\sqrt\\rho+\\eta$ & $\\ell_\\alpha$ & $s_J$ & $M$ & $s_E$ & $s_{{E,\\mathrm{{att}}}}$\\\\").unwrap();
    writeln!(tex, "\\hline").unwrap();
    for j in &jrows {
        writeln!(
            tex,
            "{} & {:.4} & {} & {} & {:.4} & {} & {}\\\\",
            j.rho_inv, j.alpha, j.ell, j.s_j, j.m, j.s_e, j.s_e_lo
        )
        .unwrap();
    }
    writeln!(tex, "\\hline\\end{{tabular}}").unwrap();
    writeln!(tex, "\\caption{{Johnson regime at $\\lambda=128$, $\\eta={}$, binary arity, with $\\eps^J_{{\\MCA}}$ set to $0$ (provisional, see \\cref{{rem:johnson-provisional}}). $s_J$: proximity, promise binding ($\\delta_0\\le\\sqrt\\rho+\\eta-\\rho$) and session uniqueness; $s_E$: non-equivocation; $s_{{E,\\mathrm{{att}}}}$: smallest $s$ not broken by \\cref{{thm:eq-attack}}.}}", ETA).unwrap();
    writeln!(tex, "\\label{{tab:johnson}}").unwrap();
    writeln!(tex, "\\end{{table}}").unwrap();

    fs::write(&out, &tex).expect("cannot write output file");

    let fs_rows: Vec<FsRow> = [2u32, 4, 8, 16].into_iter().map(fs_row).collect();
    let mut ftex = String::new();
    writeln!(ftex, "% Generated by tools/params (sfri-params). Do not edit by hand.").unwrap();
    writeln!(ftex, "\\begin{{table}}[ht]\\centering\\small").unwrap();
    writeln!(ftex, "\\renewcommand{{\\arraystretch}}{{1.15}}").unwrap();
    writeln!(ftex, "\\begin{{tabular}}{{r|rr|rr|rr}}").unwrap();
    writeln!(ftex, "\\hline").unwrap();
    writeln!(ftex, " & \\multicolumn{{2}}{{c|}}{{$\\F_{{p^3}}$, $Q=2^{{40}}$}} & \\multicolumn{{2}}{{c|}}{{$\\F_{{p^3}}$, $Q=2^{{64}}$}} & \\multicolumn{{2}}{{c}}{{$\\F_{{p^4}}$, $Q=2^{{64}}$}}\\\\").unwrap();
    writeln!(ftex, "$1/\\rho$ & $\\lambda_{{\\mathrm{{cr}}}}$ & $s$ & $\\lambda_{{\\mathrm{{cr}}}}$ & $s$ & $\\lambda_{{\\mathrm{{cr}}}}$ & $s$\\\\").unwrap();
    writeln!(ftex, "\\hline").unwrap();
    for r in &fs_rows {
        let mut line = format!("{}", r.rho_inv);
        for (_, _, bits, s) in &r.cells {
            let s_str = s.map(|v| v.to_string()).unwrap_or_else(|| "---".to_string());
            line.push_str(&format!(" & {:.1} & {}", bits, s_str));
        }
        line.push_str("\\\\");
        writeln!(ftex, "{line}").unwrap();
    }
    writeln!(ftex, "\\hline\\end{{tabular}}").unwrap();
    writeln!(ftex, "\\caption{{State-restoration unique binding at $\\lambda=128$, $L=2^{{20}}$, arity $2$. $\\lambda_{{\\mathrm{{cr}}}}=-\\log_2(Q\\,n_1/|\\K|)$ is the security of the commit rounds; $s$ is the smallest query count meeting $2^{{-128}}$ by \\cref{{thm:sr-binding}}, and --- means that the commit rounds alone exceed $2^{{-128}}$.}}").unwrap();
    writeln!(ftex, "\\label{{tab:fs}}").unwrap();
    writeln!(ftex, "\\end{{table}}").unwrap();
    fs::write(&out_fs, &ftex).expect("cannot write fs output file");

    println!("unique binding (lambda = {LAMBDA}, L = 2^{LOG2_L})");
    println!("1/rho  a   k   d  log2N  log2eps_UD  s_A  s_att  elts/path  hashes/path  KiB");
    for r in &rows {
        println!(
            "{:>5} {:>3} {:>3} {:>3} {:>6} {:>11.1} {:>4} {:>6} {:>10.0} {:>12.0} {:>5.0}",
            r.rho_inv, r.a, r.k, r.d, r.log2_n, r.log2_eps_ud, r.s_a, r.s_lo, r.k_elems, r.hashes, r.proof_kib
        );
    }
    println!();
    println!("Johnson regime (eta = {ETA}, eps^J_MCA = 0 provisional)");
    println!("1/rho   alpha  ell  s_J       M  s_E  s_E_att");
    for j in &jrows {
        println!(
            "{:>5} {:>7.4} {:>4} {:>4} {:>7.4} {:>4} {:>8}",
            j.rho_inv, j.alpha, j.ell, j.s_j, j.m, j.s_e, j.s_e_lo
        );
    }
    println!();
    println!("Fiat-Shamir (state restoration), unique binding, arity 2");
    for r in &fs_rows {
        let cells: Vec<String> = r
            .cells
            .iter()
            .map(|(e, lq, b, s)| format!("e={e} Q=2^{lq}: commit {b:.1} bits, s={}", s.map(|v| v.to_string()).unwrap_or("-".into())))
            .collect();
        println!("1/rho={}: {}", r.rho_inv, cells.join(" | "));
    }
    println!();
    println!("wrote {out} and {out_fs}");
}
