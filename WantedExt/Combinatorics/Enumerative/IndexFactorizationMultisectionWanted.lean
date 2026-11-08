/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Defs
public import MathlibExt.Analysis.SpecialFunctions.LambertSeries
public import MathlibExt.Analysis.SpecialFunctions.QPochhammer

/-!
# Multisection identities by index factorization (statements)

Statement-only targets from Vignat and Milgram, *Curious Multisection Identities by
Index Factorization*. Every positive integer is written uniquely as
`m = (2n - 1) 2^j` (more generally `m = (bn - k) b^j` with `1 ≤ k < b`), and the
paper's identities regroup a sum or product over `m` along this factorization.

Conventions: a sequence `b₁, b₂, …` is a function `b : ℕ → ℂ` whose value at `0`
is unused; the paper's index `n ≥ 1` becomes `n + 1` (or `2n + 1`, `2n + 2`) with
`n : ℕ`. Product identities over an arbitrary sequence are stated in the paper's
sum form (Section 1 of the paper: each structural product identity "translates into
a sum form"). The paper's "such that the sums exist" is read as summability (absolute
convergence) of each family that the identity regroups.
-/

namespace MetaMathlibExt

@[expose] public section

/-- Parametric `2`-adic multisection, sum form: for every `q : ℂ`,
`∑_{j ≥ 0, n ≥ 1} (q^j b_{(2n-1) 2^j} - q^j (q - 1) b_{(2n) 2^j}) = ∑_{m ≥ 1} b_m`,
whenever the two regrouped families are summable (summability of `b` follows).

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5,
Proposition 1, series version (`jis-2024-24.5.5-prop-1`). -/
public theorem_wanted tsum_twoAdic_parametric_multisection (q : ℂ) (b : ℕ → ℂ)
    (hodd : Summable fun x : ℕ × ℕ => q ^ x.1 * b ((2 * x.2 + 1) * 2 ^ x.1))
    (heven : Summable fun x : ℕ × ℕ => q ^ x.1 * (q - 1) * b ((2 * x.2 + 2) * 2 ^ x.1)) :
    ∑' x : ℕ × ℕ, (q ^ x.1 * b ((2 * x.2 + 1) * 2 ^ x.1)
        - q ^ x.1 * (q - 1) * b ((2 * x.2 + 2) * 2 ^ x.1))
      = ∑' m : ℕ, b (m + 1)

/-- Parametric `3`-adic multisection, sum form: for every `q : ℂ`,
`∑_{j ≥ 0, n ≥ 1} (q^j (b_{(3n-1) 3^j} + b_{(3n-2) 3^j}) - q^j (q - 1) b_{(3n) 3^j})
= ∑_{m ≥ 1} b_m`, whenever the three regrouped families are summable.

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5,
Corollary 6, first display in sum form (`jis-2024-24.5.5-cor-6`). -/
public theorem_wanted tsum_threeAdic_parametric_multisection (q : ℂ) (b : ℕ → ℂ)
    (h₂ : Summable fun x : ℕ × ℕ => q ^ x.1 * b ((3 * x.2 + 2) * 3 ^ x.1))
    (h₁ : Summable fun x : ℕ × ℕ => q ^ x.1 * b ((3 * x.2 + 1) * 3 ^ x.1))
    (h₃ : Summable fun x : ℕ × ℕ => q ^ x.1 * (q - 1) * b ((3 * x.2 + 3) * 3 ^ x.1)) :
    ∑' x : ℕ × ℕ, (q ^ x.1 * (b ((3 * x.2 + 2) * 3 ^ x.1) + b ((3 * x.2 + 1) * 3 ^ x.1))
        - q ^ x.1 * (q - 1) * b ((3 * x.2 + 3) * 3 ^ x.1))
      = ∑' m : ℕ, b (m + 1)

/-- The multiples of `3` regrouped by their `3`-adic factorization, sum form:
`∑_{j ≥ 1, n ≥ 1} (b_{(3n-1) 3^j} + b_{(3n-2) 3^j}) = ∑_{m ≥ 1} b_{3m}`, for `b`
summable along the multiples of `3`.

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5,
Corollary 6, deduced identity in sum form (`jis-2024-24.5.5-cor-6`). -/
public theorem_wanted tsum_threeAdic_multiples_regroup (b : ℕ → ℂ)
    (hb : Summable fun m : ℕ => b (3 * (m + 1))) :
    ∑' x : ℕ × ℕ, (b ((3 * x.2 + 2) * 3 ^ (x.1 + 1)) + b ((3 * x.2 + 1) * 3 ^ (x.1 + 1)))
      = ∑' m : ℕ, b (3 * (m + 1))

/-- Parametric base-`B` multisection, sum form: for every base `B ≥ 2` and `q : ℂ`,
`∑_{j ≥ 0, n ≥ 1} (q^j ∑_{k=1}^{B-1} c_{(Bn-k) B^j} - q^j (q - 1) c_{(Bn) B^j})
= ∑_{m ≥ 1} c_m`, whenever the two regrouped families are summable.

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5,
Proposition 7, first display in sum form (`jis-2024-24.5.5-prop-7`). -/
public theorem_wanted tsum_baseAdic_parametric_multisection (B : ℕ) (hB : 2 ≤ B) (q : ℂ)
    (c : ℕ → ℂ)
    (hlow : Summable fun x : ℕ × ℕ × Fin (B - 1) =>
      q ^ x.1 * c ((B * (x.2.1 + 1) - (x.2.2 + 1)) * B ^ x.1))
    (htop : Summable fun x : ℕ × ℕ => q ^ x.1 * (q - 1) * c (B * (x.2 + 1) * B ^ x.1)) :
    ∑' x : ℕ × ℕ, (q ^ x.1 * ∑ i : Fin (B - 1), c ((B * (x.2 + 1) - (i + 1)) * B ^ x.1)
        - q ^ x.1 * (q - 1) * c (B * (x.2 + 1) * B ^ x.1))
      = ∑' m : ℕ, c (m + 1)

/-- The multiples of `B` regrouped by their `B`-adic factorization, sum form: for
`B ≥ 2`, `∑_{j ≥ 1, n ≥ 1} ∑_{k=1}^{B-1} c_{(Bn-k) B^j} = ∑_{m ≥ 1} c_{Bm}`, for `c`
summable along the multiples of `B`.

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5,
Proposition 7, deduced identity in sum form (`jis-2024-24.5.5-prop-7`). -/
public theorem_wanted tsum_baseAdic_multiples_regroup (B : ℕ) (hB : 2 ≤ B) (c : ℕ → ℂ)
    (hc : Summable fun m : ℕ => c (B * (m + 1))) :
    ∑' x : ℕ × ℕ, ∑ i : Fin (B - 1), c ((B * (x.2 + 1) - (i + 1)) * B ^ (x.1 + 1))
      = ∑' m : ℕ, c (B * (m + 1))

/-- Weighted base-`B` multisection, sum form: for `B ≥ 2` and weights `φ, χ : ℕ → ℂ`,
`∑_{j ≥ 0, n ≥ 1} (∑_{k=1}^{B-1} φ(j) c_{(Bn-k) B^j} + χ(j) c_{(Bn) B^j})
= ∑_{m ≥ 1} (φ(ν_B(m)) + ∑_{k < ν_B(m)} χ(k)) c_m`, where `ν_B(m)` is the largest
`k` with `B^k ∣ m` (`padicValNat B m`), whenever the two regrouped families are
summable.

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5,
Proposition 8, base-`b` sum form (`jis-2024-24.5.5-prop-8`). -/
public theorem_wanted tsum_baseAdic_weighted_multisection (B : ℕ) (hB : 2 ≤ B)
    (φ χ c : ℕ → ℂ)
    (hlow : Summable fun x : ℕ × ℕ × Fin (B - 1) =>
      φ x.1 * c ((B * (x.2.1 + 1) - (x.2.2 + 1)) * B ^ x.1))
    (htop : Summable fun x : ℕ × ℕ => χ x.1 * c (B * (x.2 + 1) * B ^ x.1)) :
    ∑' x : ℕ × ℕ, (∑ i : Fin (B - 1), φ x.1 * c ((B * (x.2 + 1) - (i + 1)) * B ^ x.1)
        + χ x.1 * c (B * (x.2 + 1) * B ^ x.1))
      = ∑' m : ℕ, (φ (padicValNat B (m + 1))
          + ∑ k ∈ Finset.range (padicValNat B (m + 1)), χ k) * c (m + 1)

/-- Truncated `2`-adic regrouping, sum form: for every `J`,
`∑_{j ≥ J, n ≥ 1} φ(j) c_{(2n-1) 2^j} = ∑_{p ≥ 1} φ(J + ν₂(p)) c_{p 2^J}`.

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5,
Proposition 13, in sum form (`jis-2024-24.5.5-prop-13`). -/
public theorem_wanted tsum_twoAdic_truncated_regroup (J : ℕ) (φ c : ℕ → ℂ) :
    ∑' x : ℕ × ℕ, φ (x.1 + J) * c ((2 * x.2 + 1) * 2 ^ (x.1 + J))
      = ∑' p : ℕ, φ (J + padicValNat 2 (p + 1)) * c ((p + 1) * 2 ^ J)

/-- The multiples of `2^J` regrouped by their `2`-adic factorization, sum form:
`∑_{j ≥ J, n ≥ 1} c_{(2n-1) 2^j} = ∑_{p ≥ 1} c_{p 2^J}`.

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5,
Corollary 14, first display in sum form (`jis-2024-24.5.5-cor-14`). -/
public theorem_wanted tsum_twoAdic_high_regroup (J : ℕ) (c : ℕ → ℂ) :
    ∑' x : ℕ × ℕ, c ((2 * x.2 + 1) * 2 ^ (x.1 + J)) = ∑' p : ℕ, c ((p + 1) * 2 ^ J)

/-- The non-multiples of `2^J` regrouped by their `2`-adic factorization, sum form:
`∑_{0 ≤ j < J, n ≥ 1} c_{(2n-1) 2^j} = ∑_{p ≥ 1, 2^J ∤ p} c_p`.

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5,
Corollary 14, second display in sum form (`jis-2024-24.5.5-cor-14`). -/
public theorem_wanted tsum_twoAdic_low_regroup (J : ℕ) (c : ℕ → ℂ) :
    ∑' x : Fin J × ℕ, c ((2 * x.2 + 1) * 2 ^ (x.1 : ℕ))
      = ∑' p : {p : ℕ // 0 < p ∧ ¬ 2 ^ J ∣ p}, c p

/-- Double-indexed `2`-adic multisection, sum form:
`∑_{p, q ≥ 1} b_{p,q} = ∑_{j, k ≥ 0} ∑_{m, n ≥ 1} 2^{j+k} (b_{(2n-1)2^j, (2m-1)2^k}
+ b_{(2n)2^j, (2m)2^k} - b_{(2n)2^j, (2m-1)2^k} - b_{(2n-1)2^j, (2m)2^k})`,
whenever the four weighted families are summable.

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5,
Proposition 15, sum version (`jis-2024-24.5.5-prop-15`). -/
public theorem_wanted tsum_twoAdic_double_multisection (b : ℕ → ℕ → ℂ)
    (h₁ : Summable fun x : (ℕ × ℕ) × (ℕ × ℕ) =>
      (2 : ℂ) ^ (x.1.1 + x.1.2) * b ((2 * x.2.1 + 1) * 2 ^ x.1.1) ((2 * x.2.2 + 1) * 2 ^ x.1.2))
    (h₂ : Summable fun x : (ℕ × ℕ) × (ℕ × ℕ) =>
      (2 : ℂ) ^ (x.1.1 + x.1.2) * b ((2 * x.2.1 + 2) * 2 ^ x.1.1) ((2 * x.2.2 + 2) * 2 ^ x.1.2))
    (h₃ : Summable fun x : (ℕ × ℕ) × (ℕ × ℕ) =>
      (2 : ℂ) ^ (x.1.1 + x.1.2) * b ((2 * x.2.1 + 2) * 2 ^ x.1.1) ((2 * x.2.2 + 1) * 2 ^ x.1.2))
    (h₄ : Summable fun x : (ℕ × ℕ) × (ℕ × ℕ) =>
      (2 : ℂ) ^ (x.1.1 + x.1.2) * b ((2 * x.2.1 + 1) * 2 ^ x.1.1) ((2 * x.2.2 + 2) * 2 ^ x.1.2)) :
    ∑' p : ℕ × ℕ, b (p.1 + 1) (p.2 + 1)
      = ∑' x : (ℕ × ℕ) × (ℕ × ℕ), (2 : ℂ) ^ (x.1.1 + x.1.2)
          * (b ((2 * x.2.1 + 1) * 2 ^ x.1.1) ((2 * x.2.2 + 1) * 2 ^ x.1.2)
            + b ((2 * x.2.1 + 2) * 2 ^ x.1.1) ((2 * x.2.2 + 2) * 2 ^ x.1.2)
            - b ((2 * x.2.1 + 2) * 2 ^ x.1.1) ((2 * x.2.2 + 1) * 2 ^ x.1.2)
            - b ((2 * x.2.1 + 1) * 2 ^ x.1.1) ((2 * x.2.2 + 2) * 2 ^ x.1.2))

/-- The Lambert series `f(q) = ∑_{n ≥ 1} n q^n / (1 - q^n)` (`lambertF`) and
`g(q) = ∑_{n ≥ 1} n q^n / (1 + q^n)` (`lambertG`) satisfy, for `|q| < 1`,
`f(q) = ∑_{j, k ≥ 0} 2^{2j+k} (g(q^{2^{j+k}}) - 4 g(q^{2^{j+k+1}}))`.

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5,
Corollary 16 (`jis-2024-24.5.5-cor-16`). -/
public theorem_wanted lambert_sigma_eq_tsum_twoAdic (q : ℂ) (hq : ‖q‖ < 1) :
    lambertF ⟨q, hq⟩
      = ∑' x : ℕ × ℕ, (2 : ℂ) ^ (2 * x.1 + x.2)
          * (lambertG ⟨q ^ 2 ^ (x.1 + x.2),
              (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by positivity))⟩
            - 4 * lambertG ⟨q ^ 2 ^ (x.1 + x.2 + 1),
              (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by positivity))⟩)

/-- `2`-adic dissection of the Euler function, first display: with
`(a; r)_∞ = ∏_{k ≥ 0} (1 - a r^k)` (`QPochhammer.qPochhammerInf`), for `|q| < 1`,
`∏_{j ≥ 0} ((q^{2^j}; q^{2^{j+1}})_∞ / (q^{2^{j+1}}; q^{2^{j+1}})_∞)^{2^j} = (q; q)_∞`.

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5,
Proposition 19, first display (`jis-2024-24.5.5-prop-19`). -/
public theorem_wanted tprod_qPochhammer_twoAdic (q : ℂ) (hq : ‖q‖ < 1) :
    ∏' j : ℕ, (QPochhammer.qPochhammerInf (q ^ 2 ^ j) (q ^ 2 ^ (j + 1))
          (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by positivity))
        / QPochhammer.qPochhammerInf (q ^ 2 ^ (j + 1)) (q ^ 2 ^ (j + 1))
          (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by positivity))) ^ 2 ^ j
      = QPochhammer.qPochhammerInf q q hq

/-- Parametric `2`-adic dissection of the Euler function, for real `0 < q < 1` and
real `p`: `∏_{j ≥ 0} ((q^{2^j}; q^{2^{j+1}})_∞ / (q^{2^{j+1}}; q^{2^{j+1}})_∞^{p-1})^{p^j}
= (q; q)_∞`.

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5,
Proposition 19, second display, real case (`jis-2024-24.5.5-prop-19`). -/
public theorem_wanted tprod_qPochhammer_twoAdic_parametric (q p : ℝ) (hq₀ : 0 < q)
    (hq₁ : q < 1) :
    ∏' j : ℕ, ((∏' k : ℕ, (1 - q ^ 2 ^ j * (q ^ 2 ^ (j + 1)) ^ k))
        / (∏' k : ℕ, (1 - q ^ 2 ^ (j + 1) * (q ^ 2 ^ (j + 1)) ^ k)) ^ (p - 1)) ^ (p ^ j)
      = ∏' k : ℕ, (1 - q * q ^ k)

/-- Parametric `3`-adic dissection of the Euler function, for real `0 < q < 1` and
real `p`: `∏_{j ≥ 0} ((q^{3^j}; q^{3^{j+1}})_∞ (q^{2·3^j}; q^{3^{j+1}})_∞
/ (q^{3^{j+1}}; q^{3^{j+1}})_∞^{p-1})^{p^j} = (q; q)_∞`.

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5,
Proposition 19, third display, real case (`jis-2024-24.5.5-prop-19`). -/
public theorem_wanted tprod_qPochhammer_threeAdic_parametric (q p : ℝ) (hq₀ : 0 < q)
    (hq₁ : q < 1) :
    ∏' j : ℕ, ((∏' k : ℕ, (1 - q ^ 3 ^ j * (q ^ 3 ^ (j + 1)) ^ k))
        * (∏' k : ℕ, (1 - q ^ (2 * 3 ^ j) * (q ^ 3 ^ (j + 1)) ^ k))
        / (∏' k : ℕ, (1 - q ^ 3 ^ (j + 1) * (q ^ 3 ^ (j + 1)) ^ k)) ^ (p - 1)) ^ (p ^ j)
      = ∏' k : ℕ, (1 - q * q ^ k)

/-- `2`-adic factorization of the Euler function (the case `p = 1`): for `|q| < 1`,
`∏_{j ≥ 0} (q^{2^j}; q^{2^{j+1}})_∞ = (q; q)_∞`.

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5,
Proposition 19, case `p = 1`, base 2 (`jis-2024-24.5.5-prop-19`). -/
public theorem_wanted tprod_qPochhammer_twoAdic_factorization (q : ℂ) (hq : ‖q‖ < 1) :
    ∏' j : ℕ, QPochhammer.qPochhammerInf (q ^ 2 ^ j) (q ^ 2 ^ (j + 1))
        (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by positivity))
      = QPochhammer.qPochhammerInf q q hq

/-- `3`-adic factorization of the Euler function (the case `p = 1`): for `|q| < 1`,
`∏_{j ≥ 0} (q^{3^j}; q^{3^{j+1}})_∞ (q^{2·3^j}; q^{3^{j+1}})_∞ = (q; q)_∞`.

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5,
Proposition 19, case `p = 1`, base 3 (`jis-2024-24.5.5-prop-19`). -/
public theorem_wanted tprod_qPochhammer_threeAdic_factorization (q : ℂ) (hq : ‖q‖ < 1) :
    ∏' j : ℕ, (QPochhammer.qPochhammerInf (q ^ 3 ^ j) (q ^ 3 ^ (j + 1))
          (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by positivity))
        * QPochhammer.qPochhammerInf (q ^ (2 * 3 ^ j)) (q ^ 3 ^ (j + 1))
          (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by positivity)))
      = QPochhammer.qPochhammerInf q q hq

/-- `2`-adic multisection of the `q`-Pochhammer symbol: for `a : ℂ` and `|q| < 1`,
`∏_{j ≥ 0} ((a q^{2^j - 1}; q^{2^{j+1}})_∞ / (a q^{2^{j+1} - 1}; q^{2^{j+1}})_∞)^{2^j}
= (a; q)_∞`.

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5,
Proposition 20 (`jis-2024-24.5.5-prop-20`). -/
public theorem_wanted tprod_qPochhammer_shifted_twoAdic (a q : ℂ) (hq : ‖q‖ < 1) :
    ∏' j : ℕ, (QPochhammer.qPochhammerInf (a * q ^ (2 ^ j - 1)) (q ^ 2 ^ (j + 1))
          (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by positivity))
        / QPochhammer.qPochhammerInf (a * q ^ (2 ^ (j + 1) - 1)) (q ^ 2 ^ (j + 1))
          (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by positivity))) ^ 2 ^ j
      = QPochhammer.qPochhammerInf a q hq

/-- `2`-adic dissection of `f(a, z) = Γ(a+1)² / (Γ(a+1-iz) Γ(a+1+iz))`: for `a` not a
negative integer and every `z : ℂ`,
`f(a, z) = ∏_{j ≥ 0} f(a / 2^{j+1} - 1/2, z / 2^{j+1})`, written out with
`a / 2^{j+1} - 1/2 + 1 = a / 2^{j+1} + 1/2` as in the paper's explicit form.

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5,
Proposition 22 (`jis-2024-24.5.5-prop-22`). -/
public theorem_wanted gamma_ratio_eq_tprod_twoAdic (a z : ℂ)
    (ha : ∀ n : ℕ, a ≠ -((n : ℂ) + 1)) :
    Complex.Gamma (a + 1) ^ 2
        / (Complex.Gamma (a + 1 - Complex.I * z) * Complex.Gamma (a + 1 + Complex.I * z))
      = ∏' j : ℕ, Complex.Gamma (a / 2 ^ (j + 1) + 1 / 2) ^ 2
          / (Complex.Gamma (a / 2 ^ (j + 1) + 1 / 2 - Complex.I * (z / 2 ^ (j + 1)))
            * Complex.Gamma (a / 2 ^ (j + 1) + 1 / 2 + Complex.I * (z / 2 ^ (j + 1))))


/-- `f_μ` and `g_μ`: for `μ ≥ 1` and `|q| < 1`, the Lambert series
`f_μ(q) = ∑_{n ≥ 1} n^μ qⁿ / (1 - qⁿ)` (`lambertFMu`) and `g_μ(q) = ∑_{n ≥ 1} n^μ qⁿ / (1 + qⁿ)`
(`lambertGMu`) satisfy
`f_μ(q) = ∑_{j, k ≥ 0} 2^{(μ+1)j+k} (g_μ(q^{2^{j+k}}) - 2^{μ+1} g_μ(q^{2^{j+k+1}}))`.
Corrected reading: the paper prints the weight `2^{2j+k}`, its value for `μ = 1`
(Corollary 16), which is false for `μ ≥ 2` (`μ = 2`: the coefficient of `q²` is `σ₂(2) = 5` on
the left and `1` on the right). The weight `2^{(μ+1)j+k}` is what the paper's proof of
Corollary 16 gives with `n^μ` in place of `n`: there `2^{2j+k} = 2^{j+k} · 2^j`, where `2^j` is
the factor of the index `(2n-1) 2^j` in the summand `n`, which becomes `2^{μ j}` for `n^μ`.

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5, Corollary 17 (`jis-2024-24.5.5-cor-17`). -/
public theorem_wanted lambertMu_sigma_eq_tsum_twoAdic (μ : {μ : ℕ // 1 ≤ μ}) (q : ℂ)
    (hq : ‖q‖ < 1) :
    lambertFMu ⟨q, hq⟩ μ
      = ∑' x : ℕ × ℕ, (2 : ℂ) ^ (((μ : ℕ) + 1) * x.1 + x.2)
          * (lambertGMu ⟨q ^ 2 ^ (x.1 + x.2),
              (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by positivity))⟩ μ
            - 2 ^ ((μ : ℕ) + 1) * lambertGMu ⟨q ^ 2 ^ (x.1 + x.2 + 1),
              (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by positivity))⟩ μ)

/-- The Borwein eta-Lambert correspondence: for sequences `(a_n)`, `(b_n)` with polynomial
growth `|a_n|, |b_n| ≤ C n^K` (`n ≥ 1`),
`η(s) ∑_{n ≥ 1} a_n / n^s = ∑_{n ≥ 1} b_n / n^s` for all real `s > max (K + 2) 1` if and only if
`∑_{n ≥ 1} a_n xⁿ / (1 + xⁿ) = ∑_{n ≥ 1} b_n xⁿ` for all `0 < x < 1`, where
`η(s) = ∑_{n ≥ 1} (-1)^{n-1} / n^s` is the Dirichlet eta function (Mathlib's `LSeries` of
`(-1)^{n+1}`). The paper quotes this from Borwein and Borwein with no growth hypotheses or
domains; polynomial growth and the half-line `s > max (K + 2) 1` (absolute convergence of all
three series; `s > 1` is needed for `η` itself when `K < -1`) and interval
`0 < x < 1` are added so that both sides are defined. The values `a 0`, `b 0` are unused.

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5, Proposition 18 (`jis-2024-24.5.5-prop-18`). -/
public theorem_wanted eta_mul_LSeries_iff_lambert (a b : ℕ → ℂ) (C K : ℝ)
    (ha : ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ C * (n : ℝ) ^ K)
    (hb : ∀ n : ℕ, 1 ≤ n → ‖b n‖ ≤ C * (n : ℝ) ^ K) :
    (∀ s : ℝ, max (K + 2) 1 < s →
      LSeries (fun n : ℕ => (-1 : ℂ) ^ (n + 1)) s * LSeries a s = LSeries b s) ↔
    ∀ x : ℝ, 0 < x → x < 1 →
      ∑' n : ℕ, a (n + 1) * (x : ℂ) ^ (n + 1) / (1 + (x : ℂ) ^ (n + 1)) =
        ∑' n : ℕ, b (n + 1) * (x : ℂ) ^ (n + 1)

/-- The function `g(a, b, z) = b/(b - z) · Γ(a - √(a² - b)) Γ(a + √(a² - b)) /
(Γ(a - √(a² - b + z)) Γ(a + √(a² - b + z)))`, with the principal complex square root (the value
does not depend on the choice of root).

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5, Proposition 23. -/
public noncomputable def gammaQuadraticRatio (a b z : ℂ) : ℂ :=
  b / (b - z) * (Complex.Gamma (a - (a ^ 2 - b) ^ (1 / 2 : ℂ))
      * Complex.Gamma (a + (a ^ 2 - b) ^ (1 / 2 : ℂ)))
    / (Complex.Gamma (a - (a ^ 2 - b + z) ^ (1 / 2 : ℂ))
      * Complex.Gamma (a + (a ^ 2 - b + z) ^ (1 / 2 : ℂ)))

/-- `g(a, b, 0) = 1` when `b ≠ 0` and the Gamma values are nonzero.

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5, Proposition 23. -/
public theorem gammaQuadraticRatio_zero_right (a b : ℂ) (hb : b ≠ 0)
    (hΓ : Complex.Gamma (a - (a ^ 2 - b) ^ (1 / 2 : ℂ))
      * Complex.Gamma (a + (a ^ 2 - b) ^ (1 / 2 : ℂ)) ≠ 0) :
    gammaQuadraticRatio a b 0 = 1 := by
  simp only [gammaQuadraticRatio, sub_zero, add_zero]
  rw [div_self hb, one_mul, div_self hΓ]

/-- `2`-adic dissection of `g(a, b, z)`: if `m² + 2am + b ≠ 0` and `m² + 2am + b - z ≠ 0` for
every integer `m ≥ 0` and every `m = -2^j` (`j ≥ 0`), then
`g(a, b, z) = ∏_{j ≥ 0} g(a/2^{j+1} - 1/2, 1/4 - a/2^{j+1} + b/2^{2j+2}, z/2^{2j+2})`.
Corrected reading: the paper prints the parameters `a/2^j - 1` and `1 - a/2^{j+1} + b/2^{2j+2}`,
which is false even under the hypotheses below (`a = 3/10`, `b = -2`, `z = 7/10`: numerically
`g(a, b, z) ≈ 1.6283`, while the printed product is `≈ 6.18 · 10⁴` and the corrected one matches). The corrected parameters are those of the penultimate line of the paper's proof,
`m² + 2am + b = 2^{2j+2}(n² + n(a/2^j - 1) + (1/4 + b/2^{2j+2} - a/2^{j+1}))` for
`m = (2n - 1) 2^j`, from which the printed last step drops the factor `1/2` in the linear
coefficient and `1/4` in the constant. The hypotheses exclude poles of every Gamma factor on both
sides and zero prefactors `b`, `b - z` (the paper states none): `Γ(a ± √(a² - b))` has a pole
exactly when `n² + 2an + b = 0` for some `n ≥ 0`, and the `j`th factor on the right exactly
when `m² + 2am + b = 0` for `m = (2n - 1) 2^j`, `n ≥ 0`, i.e. `m = -2^j` or `m > 0`; other
integer roots (e.g. `m = -3` for `a = 5/4`, `b = -3/2`) are allowed.

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5, Proposition 23 (`jis-2024-24.5.5-prop-23`). -/
public theorem_wanted gammaQuadraticRatio_eq_tprod_twoAdic (a b z : ℂ)
    (hb : ∀ m : ℤ, (0 ≤ m ∨ ∃ j : ℕ, m = -2 ^ j) → (m : ℂ) ^ 2 + 2 * a * m + b ≠ 0)
    (hz : ∀ m : ℤ, (0 ≤ m ∨ ∃ j : ℕ, m = -2 ^ j) → (m : ℂ) ^ 2 + 2 * a * m + b - z ≠ 0) :
    gammaQuadraticRatio a b z
      = ∏' j : ℕ, gammaQuadraticRatio (a / 2 ^ (j + 1) - 1 / 2)
          (1 / 4 - a / 2 ^ (j + 1) + b / 2 ^ (2 * j + 2)) (z / 2 ^ (2 * j + 2))

end

end MetaMathlibExt
