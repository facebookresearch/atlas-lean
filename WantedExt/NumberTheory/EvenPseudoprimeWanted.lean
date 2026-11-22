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
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Lemma 2.** If an odd prime `p` divides an even pseudoprime `N`, then
`N ≡ p (mod p ℓ₂(p))`, `ℓ₂(p)` is odd, `p ≡ ±1 (mod 8)` and `p ≤ N / 14`.

Source: Cheng, Kinlaw and Nguyen, *The Reciprocal Sum of Even Pseudoprimes*, Journal of
Integer Sequences 29 (2026), Article 26.1.3, Lemma 2 (`jis-2026-26.1.3-lem-2`). -/
public theorem_wanted evenPseudoprime_modEq_and_orderOf_odd {N p : ℕ} (hN : MathlibExt.NumberTheory.IsEvenPseudoprime N)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpN : p ∣ N) :
    N ≡ p [MOD p * orderOf (2 : ZMod p)] ∧ Odd (orderOf (2 : ZMod p)) ∧
      (p % 8 = 1 ∨ p % 8 = 7) ∧ 14 * p ≤ N

/-- **Corollary 4.** Every even pseudoprime is `≡ 2` or `14 (mod 16)`.

Source: Cheng, Kinlaw and Nguyen, *The Reciprocal Sum of Even Pseudoprimes*, Journal of
Integer Sequences 29 (2026), Article 26.1.3, Corollary 4 (`jis-2026-26.1.3-cor-4`). -/
public theorem_wanted evenPseudoprime_mod_sixteen {N : ℕ} (hN : MathlibExt.NumberTheory.IsEvenPseudoprime N) :
    N % 16 = 2 ∨ N % 16 = 14

/-- **Lemma 5.** If `p² ∣ N` for an even pseudoprime `N` and a prime `p`, then `p` is a
Wieferich prime, `2^{p-1} ≡ 1 (mod p²)`; in particular `p ≥ 3511`.

Source: Cheng, Kinlaw and Nguyen, *The Reciprocal Sum of Even Pseudoprimes*, Journal of
Integer Sequences 29 (2026), Article 26.1.3, Lemma 5 (`jis-2026-26.1.3-lem-5`). -/
public theorem_wanted evenPseudoprime_wieferich_of_sq_dvd {N p : ℕ} (hN : MathlibExt.NumberTheory.IsEvenPseudoprime N)
    (hp : p.Prime) (hpN : p ^ 2 ∣ N) :
    2 ^ (p - 1) ≡ 1 [MOD p ^ 2] ∧ 3511 ≤ p

open scoped Classical in
/-- **Proposition 11.** For an odd prime `p` and `k ∈ ℕ`,
`F_p(k) = ∑ 1/N ≤ 2 / (p ℓ₂(p))`, the sum over `e^k < N ≤ e^{k+1}` with
`N ≡ p (mod p ℓ₂(p))` and `N > p`.

Stated for every `k ∈ ℕ`: the bound holds for all `k`, since the terms are `p + j p ℓ₂(p)`
with `j ≥ 1`.

Source: Cheng, Kinlaw and Nguyen, *The Reciprocal Sum of Even Pseudoprimes*, Journal of
Integer Sequences 29 (2026), Article 26.1.3, Proposition 11 (`jis-2026-26.1.3-prop-11`). -/
public theorem_wanted sum_inv_modEq_orderOf_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (k : ℕ) :
    ∑ N ∈ (Finset.Icc 1 ⌊Real.exp (k + 1)⌋₊).filter (fun N : ℕ =>
        Real.exp k < N ∧ N ≡ p [MOD p * orderOf (2 : ZMod p)] ∧ p < N), (1 : ℝ) / N ≤
      2 / (p * orderOf (2 : ZMod p))

open scoped Classical in
/-- **Proposition 12.** Let `p` be a prime with `p` and `ℓ₂(p)` odd and `k ∈ ℕ`, and let
`S` be the sum of `1/N` over `e^k < N ≤ e^{k+1}` with `N ≡ p (mod p ℓ₂(p))` and
`N ≡ ±2 (mod 16)`. Then `S ≤ 1 / (4 p ℓ₂(p))` whenever `16 p ℓ₂(p) ≤ e^k`, and always
`S ≤ (1/8 + 4 e^{-k} p ℓ₂(p)) / (p ℓ₂(p))`.

Partial: the clauses involving `z_k`, `c_k` and `d_k` are omitted (`z_k` is defined only in
the paper body).

Source: Cheng, Kinlaw and Nguyen, *The Reciprocal Sum of Even Pseudoprimes*, Journal of
Integer Sequences 29 (2026), Article 26.1.3, Proposition 12 (`jis-2026-26.1.3-prop-12`). -/
public theorem_wanted sum_inv_modEq_orderOf_mod_sixteen_le {p : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (hl : Odd (orderOf (2 : ZMod p))) (k : ℕ) :
    let S := ∑ N ∈ (Finset.Icc 1 ⌊Real.exp (k + 1)⌋₊).filter (fun N : ℕ =>
        Real.exp k < N ∧ N ≡ p [MOD p * orderOf (2 : ZMod p)] ∧ (N % 16 = 2 ∨ N % 16 = 14)),
      (1 : ℝ) / N
    (16 * p * orderOf (2 : ZMod p) ≤ Real.exp k → S ≤ 1 / (4 * p * orderOf (2 : ZMod p))) ∧
      S ≤ (1 / 8 + 4 * Real.exp (-k) * p * orderOf (2 : ZMod p)) / (p * orderOf (2 : ZMod p))


/-- **Lemma 8** (Nguyen and Pomerance), Rankin bound: for `2 ≤ y < x` and `0 < s < 1`,
`S(x, y) ≤ x^{-s} ζ(1 - s, y)`, where `S(x, y) = ∑_{n > x, P(n) ≤ y} 1/n` and
`ζ(σ, y) = ∑_{P(n) ≤ y} n^{-σ}` (both series converge).  The `y`-smooth positive integers
(`P(n) ≤ y`, with `P(1) = 1`) are `Nat.smoothNumbers (⌊y⌋₊ + 1)`.

Source: Cheng, Kinlaw and Nguyen, *The Reciprocal Sum of Even Pseudoprimes*, Journal of
Integer Sequences 29 (2026), Article 26.1.3, Lemma 8, display (smooth1)
(`jis-2026-26.1.3-lem-8`). -/
public theorem_wanted smoothReciprocalTail_le_rpow_mul_smoothZeta {x y s : ℝ} (hy : 2 ≤ y)
    (hyx : y < x) (hs0 : 0 < s) (hs1 : s < 1) :
    ∑' n : {n : ℕ // n ∈ Nat.smoothNumbers (⌊y⌋₊ + 1) ∧ x < n}, (1 : ℝ) / n ≤
      x ^ (-s) * ∑' n : Nat.smoothNumbers (⌊y⌋₊ + 1), (n : ℝ) ^ (-(1 - s))

/-- **Lemma 8** (Nguyen and Pomerance), explicit bound: for `2 ≤ y < x`, with
`u = log x / log y` and `s = log (u log u) / log y`, if `u ≥ 3` and `s ≤ 1/3` then
`S(x, y) ≤ x^{-s} ζ(1 - s, y) < 25 e^{(1 + ε) u} (u log u)^{-u} (2^s - 1)^{-1}` with
`ε = 2.3 · 10⁻⁸`; `S` and `ζ` as in `smoothReciprocalTail_le_rpow_mul_smoothZeta`.

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
/-- **Lemma 10**, first part: `Q_{0,a₁}(x) < M x^{2a₁}` with `a₁ = 0.4`, `M = 0.00754`,
where `Q_{a,b}(x)` counts the primes `2 < p ≤ x` with `ℓ₂(p)` odd and
`p^a < ℓ₂(p) ≤ p^b`.

Corrected range: stated for `x > 0`.  The paper says `x ≥ 0`, but at `x = 0` both sides are `0`
(`Q_{0,a₁}(0) = 0` and `M · 0^{0.8} = 0`), so the strict inequality fails there; the paper
itself applies the lemma for `t > 0`.

Source: Cheng, Kinlaw and Nguyen, *The Reciprocal Sum of Even Pseudoprimes*, Journal of
Integer Sequences 29 (2026), Article 26.1.3, Lemma 10 (`jis-2026-26.1.3-lem-10`). -/
public theorem_wanted orderOfTwo_odd_small_count_lt {x : ℝ} (hx : 0 < x) :
    ((((Finset.Icc 1 ⌊x⌋₊).filter fun p : ℕ => p.Prime ∧ 2 < p ∧
        Odd (orderOf (2 : ZMod p)) ∧ (1 : ℝ) < orderOf (2 : ZMod p) ∧
        (orderOf (2 : ZMod p) : ℝ) ≤ (p : ℝ) ^ (2 / 5 : ℝ)).card : ℕ) : ℝ) <
      754 / 100000 * x ^ (4 / 5 : ℝ)

open scoped Classical in
/-- **Lemma 10**, second part: `Q_{a₁,a₂}(x) < M x^{2a₂}` for `x ≥ 337`, with `a₁ = 0.4`,
`a₂ = 0.48`, `M = 0.00754`.

Source: Cheng, Kinlaw and Nguyen, *The Reciprocal Sum of Even Pseudoprimes*, Journal of
Integer Sequences 29 (2026), Article 26.1.3, Lemma 10 (`jis-2026-26.1.3-lem-10`). -/
public theorem_wanted orderOfTwo_odd_medium_count_lt {x : ℝ} (hx : 337 ≤ x) :
    ((((Finset.Icc 1 ⌊x⌋₊).filter fun p : ℕ => p.Prime ∧ 2 < p ∧
        Odd (orderOf (2 : ZMod p)) ∧ (p : ℝ) ^ (2 / 5 : ℝ) < orderOf (2 : ZMod p) ∧
        (orderOf (2 : ZMod p) : ℝ) ≤ (p : ℝ) ^ (12 / 25 : ℝ)).card : ℕ) : ℝ) <
      754 / 100000 * x ^ (24 / 25 : ℝ)

end

end MetaMathlibExt
