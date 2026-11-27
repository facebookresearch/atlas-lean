/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.SmoothNumbers
public import MathlibExt.NumberTheory.EvenPseudoprime
public import MathlibExt.NumberTheory.EvenPseudoprimeReciprocalWindow
public import MathlibExt.NumberTheory.EvenPseudoprimeResidueSixteen
public import MathlibExt.NumberTheory.EvenPseudoprimeWieferich

/-!
# The reciprocal sum of even pseudoprimes

Statements from Xuyan Cheng, Paul Kinlaw and Duc Nguyen, *The Reciprocal Sum of Even
Pseudoprimes*, Journal of Integer Sequences 29 (2026), Article 26.1.3.

Even pseudoprimes (even `N > 2` with `2^N ≡ 2 (mod N)`; Lehmer's smallest example is
`161038`) are the shared `MathlibExt.NumberTheory.IsEvenPseudoprime`; the paper's main
theorem (Theorem 1) is
`MathlibExt.NumberTheory.EvenPseudoprimesWanted.evenPseudoprime_reciprocal_sum_bounds` and is
not restated, nor is Lemma 6 (Dusart's bounds, the existing `dusart_pi_lower` and
`dusart_pi_upper`). `ℓ₂(p)` is the multiplicative order of `2` modulo `p`,
written `orderOf (2 : ZMod p)`.

Proved in `MathlibExt.NumberTheory.EvenPseudoprimeWieferich`, which this module imports:
`evenPseudoprime_wieferich_of_sq_dvd` (a prime whose square divides an even pseudoprime is a
Wieferich prime, at least `3511`).

Proved in `MathlibExt.NumberTheory.EvenPseudoprimeReciprocalWindow`, which this module imports:
`sum_inv_modEq_orderOf_le` (Proposition 11, the sum of `1 / N` over the integers `N` with
`e ^ k < N ≤ e ^ (k + 1)`, `N ≡ p [MOD p * ℓ₂(p)]` and `N > p` is at most `2 / (p * ℓ₂(p))`).
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Odd prime divisors of an even pseudoprime.** Let $N$ be an even pseudoprime and $p$ an
odd prime dividing $N$, and write $\ell_2(p)$ for the multiplicative order of $2$ modulo $p$.
Then $N \equiv p \pmod{p\,\ell_2(p)}$, $\ell_2(p)$ is odd, $p \equiv 1$ or $7 \pmod 8$, and
$14p \le N$.

Source: Cheng, Kinlaw and Nguyen, *The Reciprocal Sum of Even Pseudoprimes*, Journal of
Integer Sequences 29 (2026), Article 26.1.3, Lemma 2 (`jis-2026-26.1.3-lem-2`). -/
public theorem_wanted evenPseudoprime_modEq_and_orderOf_odd {N p : ℕ} (hN : MathlibExt.NumberTheory.IsEvenPseudoprime N)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpN : p ∣ N) :
    N ≡ p [MOD p * orderOf (2 : ZMod p)] ∧ Odd (orderOf (2 : ZMod p)) ∧
      (p % 8 = 1 ∨ p % 8 = 7) ∧ 14 * p ≤ N

open scoped Classical in
/-- **Reciprocal sum over a residue class restricted modulo 16.** Write $\ell_2(p)$ for the
multiplicative order of $2$ modulo a prime $p$. Let $p$ be an odd prime with $\ell_2(p)$ odd,
let $k$ be a natural number, and let $S$ be the sum of $1/N$ over the integers $N$ with
$e^k < N \le e^{k+1}$, $N \equiv p \pmod{p\,\ell_2(p)}$ and $N \equiv \pm 2 \pmod{16}$. Then
$S \le 1 / (4p\,\ell_2(p))$ whenever $16p\,\ell_2(p) \le e^k$, and in all cases
$S \le (1/8 + 4e^{-k} p\,\ell_2(p)) / (p\,\ell_2(p))$.

The paper's further clauses, involving $z_k$, $c_k$ and $d_k$, are not stated here.

Source: Cheng, Kinlaw and Nguyen, *The Reciprocal Sum of Even Pseudoprimes*, Journal of
Integer Sequences 29 (2026), Article 26.1.3, Proposition 12 (`jis-2026-26.1.3-prop-12`). -/
public theorem_wanted sum_inv_modEq_orderOf_mod_sixteen_le {p : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (hl : Odd (orderOf (2 : ZMod p))) (k : ℕ) :
    let S := ∑ N ∈ (Finset.Icc 1 ⌊Real.exp (k + 1)⌋₊).filter (fun N : ℕ =>
        Real.exp k < N ∧ N ≡ p [MOD p * orderOf (2 : ZMod p)] ∧ (N % 16 = 2 ∨ N % 16 = 14)),
      (1 : ℝ) / N
    (16 * p * orderOf (2 : ZMod p) ≤ Real.exp k → S ≤ 1 / (4 * p * orderOf (2 : ZMod p))) ∧
      S ≤ (1 / 8 + 4 * Real.exp (-k) * p * orderOf (2 : ZMod p)) / (p * orderOf (2 : ZMod p))


/-- **Rankin's bound for reciprocal sums of smooth numbers.** Let $x, y, s$ be real numbers with
$2 \le y < x$ and $0 < s < 1$. Call a positive integer $y$-smooth if all its prime factors are
at most $y$ (so $1$ is $y$-smooth). Let $S(x, y)$ be the sum of $1/n$ over the $y$-smooth
integers $n > x$, and let $\zeta(\sigma, y)$ be the sum of $n^{-\sigma}$ over all $y$-smooth
integers $n$. Then $S(x, y) \le x^{-s} \zeta(1 - s, y)$.

Both sums are unconditional sums of real numbers, which take the value $0$ for a family that is
not summable; the statement asserts only the inequality between these values, not that the
series converge.

Source: Cheng, Kinlaw and Nguyen, *The Reciprocal Sum of Even Pseudoprimes*, Journal of
Integer Sequences 29 (2026), Article 26.1.3, Lemma 8, display (smooth1)
(`jis-2026-26.1.3-lem-8`). -/
public theorem_wanted smoothReciprocalTail_le_rpow_mul_smoothZeta {x y s : ℝ} (hy : 2 ≤ y)
    (hyx : y < x) (hs0 : 0 < s) (hs1 : s < 1) :
    ∑' n : {n : ℕ // n ∈ Nat.smoothNumbers (⌊y⌋₊ + 1) ∧ x < n}, (1 : ℝ) / n ≤
      x ^ (-s) * ∑' n : Nat.smoothNumbers (⌊y⌋₊ + 1), (n : ℝ) ^ (-(1 - s))

/-- **Nguyen–Pomerance bound for reciprocal sums of smooth numbers.** Let $x, y$ be real numbers
with $2 \le y < x$. Call a positive integer $y$-smooth if all its prime factors are at most $y$,
let $S(x, y)$ be the sum of $1/n$ over the $y$-smooth integers $n > x$, and let
$\zeta(\sigma, y)$ be the sum of $n^{-\sigma}$ over all $y$-smooth integers $n$. Put
$u = \log x / \log y$ and $s = \log(u \log u) / \log y$. If $u \ge 3$ and $s \le 1/3$, then
$$
S(x, y) \le x^{-s} \zeta(1 - s, y) < 25\, e^{(1 + \varepsilon) u} (u \log u)^{-u} (2^s - 1)^{-1}
$$
with $\varepsilon = 2.3 \cdot 10^{-8}$.

Source: Cheng, Kinlaw and Nguyen, *The Reciprocal Sum of Even Pseudoprimes*, Journal of
Integer Sequences 29 (2026), Article 26.1.3, Lemma 8, display (smooth2)
(`jis-2026-26.1.3-lem-8`). -/
public theorem_wanted smoothReciprocalTail_lt_nguyenPomerance {x y : ℝ} (hy : 2 ≤ y)
    (hyx : y < x) :
    let u := Real.log x / Real.log y
    let s := Real.log (u * Real.log u) / Real.log y
    3 ≤ u → s ≤ 1 / 3 →
      ∑' n : {n : ℕ // n ∈ Nat.smoothNumbers (⌊y⌋₊ + 1) ∧ x < n}, (1 : ℝ) / n ≤
          x ^ (-s) * ∑' n : Nat.smoothNumbers (⌊y⌋₊ + 1), (n : ℝ) ^ (-(1 - s)) ∧
        x ^ (-s) * ∑' n : Nat.smoothNumbers (⌊y⌋₊ + 1), (n : ℝ) ^ (-(1 - s)) <
          25 * Real.exp ((1 + 23 / 10 ^ 9) * u) * (u * Real.log u) ^ (-u) * (2 ^ s - 1)⁻¹

open scoped Classical in
/-- **Primes with odd order of 2 of small size.** Write $\ell_2(p)$ for the multiplicative
order of $2$ modulo a prime $p$. For every real $x > 0$, the number of primes $p$ with
$2 < p \le x$ such that $\ell_2(p)$ is odd and $1 < \ell_2(p) \le p^{2/5}$ is less than
$0.00754\, x^{4/5}$.

The hypothesis $x > 0$ cannot be dropped: at $x = 0$ both sides are $0$, so the strict
inequality fails.

Source: Cheng, Kinlaw and Nguyen, *The Reciprocal Sum of Even Pseudoprimes*, Journal of
Integer Sequences 29 (2026), Article 26.1.3, Lemma 10 (`jis-2026-26.1.3-lem-10`). -/
public theorem_wanted orderOfTwo_odd_small_count_lt {x : ℝ} (hx : 0 < x) :
    ((((Finset.Icc 1 ⌊x⌋₊).filter fun p : ℕ => p.Prime ∧ 2 < p ∧
        Odd (orderOf (2 : ZMod p)) ∧ (1 : ℝ) < orderOf (2 : ZMod p) ∧
        (orderOf (2 : ZMod p) : ℝ) ≤ (p : ℝ) ^ (2 / 5 : ℝ)).card : ℕ) : ℝ) <
      754 / 100000 * x ^ (4 / 5 : ℝ)

open scoped Classical in
/-- **Primes with odd order of 2 of medium size.** Write $\ell_2(p)$ for the multiplicative
order of $2$ modulo a prime $p$. For every real $x \ge 337$, the number of primes $p$ with
$2 < p \le x$ such that $\ell_2(p)$ is odd and $p^{2/5} < \ell_2(p) \le p^{12/25}$ is less than
$0.00754\, x^{24/25}$.

Source: Cheng, Kinlaw and Nguyen, *The Reciprocal Sum of Even Pseudoprimes*, Journal of
Integer Sequences 29 (2026), Article 26.1.3, Lemma 10 (`jis-2026-26.1.3-lem-10`). -/
public theorem_wanted orderOfTwo_odd_medium_count_lt {x : ℝ} (hx : 337 ≤ x) :
    ((((Finset.Icc 1 ⌊x⌋₊).filter fun p : ℕ => p.Prime ∧ 2 < p ∧
        Odd (orderOf (2 : ZMod p)) ∧ (p : ℝ) ^ (2 / 5 : ℝ) < orderOf (2 : ZMod p) ∧
        (orderOf (2 : ZMod p) : ℝ) ≤ (p : ℝ) ^ (12 / 25 : ℝ)).card : ℕ) : ℝ) <
      754 / 100000 * x ^ (24 / 25 : ℝ)

end

end MetaMathlibExt
