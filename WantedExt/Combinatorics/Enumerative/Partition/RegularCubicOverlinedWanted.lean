/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
public import MathlibExt.Combinatorics.Enumerative.Partition.QEulerProduct

/-!
# Congruences for `ℓ`-regular cubic partitions with odd parts overlined (statements)

Statements from Pujashree Buragohain and Nipen Saikia, *Some New Congruences for l-Regular
Cubic Partitions with Odd Parts Overlined*, INTEGERS 24 (2024), Article A101.

Naika and Harishkumar's `a_ℓ(n)` counts the `ℓ`-regular cubic partitions of `n` in which the
first occurrence of each distinct odd part may be overlined; for `ℓ > 2` its generating
function is `∑ a_ℓ(n) qⁿ = f_2 f_ℓ² f_{4ℓ} / (f_1² f_4 f_{2ℓ})` (paper, eq. (2)), where
`f_k = (q^k; q^k)_∞` is `qEulerProduct k`, written `𝔣 k` below. We define `a_ℓ(n)` as the
`n`th coefficient of that quotient in `ℤ⟦X⟧` (the denominator has constant coefficient `1`).
Ramanujan's `ψ(q^k) = f_{2k}² / f_k` (paper, eq. (3)); congruences between power series are
stated coefficientwise, with a unit denominator `f_k` cleared by multiplying both sides
(this preserves congruences, since `f_k` and its inverse have integer coefficients).

Already stated elsewhere in this library: Lemma 1 (Cui–Gu `p`-dissection of `f_1`, with the
non-congruence) is `eulerProduct_p_dissection`; Lemma 2 (`p`-dissection of `ψ`) is
`ramanujanPsi_prime_dissection`; Lemma 4 is the case `k = 1` of
`qEulerProduct_pow_prime_pow_congruence`. Of Lemma 3, identities (5), (6), (7), (8), (11),
(12), (15) are `one_div_f1_sq_two_dissection`, the first conjunct of
`one_div_f1_pow_four_eight_twelve_two_dissection`, `f1_sq_two_dissection`,
`f2_sq_div_f1_dissection`, `f3_div_f1_cube_two_dissection`, `f4_div_f1_dissection` and
`f9_div_f1_two_dissection`; the remaining (9), (10), (13), (14) are
`f3_f5_quotients_two_dissection` below.
-/

open PowerSeries

namespace MetaMathlibExt

@[expose] public section

local notation "𝔣" => qEulerProduct

/-- The generating function `∑ a_ℓ(n) qⁿ = f_2 f_ℓ² f_{4ℓ} / (f_1² f_4 f_{2ℓ})` of
`ℓ`-regular cubic partitions with odd parts overlined, as an integer power series
(meaningful for `ℓ ≥ 1`; the paper uses `ℓ > 2`).

Source: Pujashree Buragohain and Nipen Saikia, *Some New Congruences for l-Regular Cubic
Partitions with Odd Parts Overlined*, INTEGERS 24 (2024), Article A101, Section 1, eq. (2). -/
public noncomputable def regularCubicOverlinedSeries (l : ℕ) : ℤ⟦X⟧ :=
  𝔣 2 * 𝔣 l ^ 2 * 𝔣 (4 * l) * invOfUnit (𝔣 1 ^ 2 * 𝔣 4 * 𝔣 (2 * l)) 1

/-- `a_ℓ(n)`, the number of `ℓ`-regular cubic partitions of `n` with the first occurrence of
each distinct odd part possibly overlined, defined as the `n`th coefficient of
`f_2 f_ℓ² f_{4ℓ} / (f_1² f_4 f_{2ℓ})` (for example `a_3(5) = 18`).

Source: Pujashree Buragohain and Nipen Saikia, *Some New Congruences for l-Regular Cubic
Partitions with Odd Parts Overlined*, INTEGERS 24 (2024), Article A101, Section 1, eq. (2). -/
public noncomputable def regularCubicOverlinedCount (l n : ℕ) : ℤ :=
  coeff n (regularCubicOverlinedSeries l)

/-- The defining identity `f_1² f_4 f_{2ℓ} ∑ a_ℓ(n) qⁿ = f_2 f_ℓ² f_{4ℓ}` for `ℓ ≥ 1`.

Source: Pujashree Buragohain and Nipen Saikia, *Some New Congruences for l-Regular Cubic
Partitions with Odd Parts Overlined*, INTEGERS 24 (2024), Article A101, Section 1, eq. (2). -/
public theorem regularCubicOverlinedCount_generatingFunction {l : ℕ} (hl : 1 ≤ l) :
    𝔣 1 ^ 2 * 𝔣 4 * 𝔣 (2 * l) * PowerSeries.mk (regularCubicOverlinedCount l) =
      𝔣 2 * 𝔣 l ^ 2 * 𝔣 (4 * l) := by
  have hmk : PowerSeries.mk (regularCubicOverlinedCount l) = regularCubicOverlinedSeries l := by
    ext n
    simp [regularCubicOverlinedCount]
  have hc : constantCoeff (𝔣 1 ^ 2 * 𝔣 4 * 𝔣 (2 * l)) = ((1 : ℤˣ) : ℤ) := by
    simp [constantCoeff_qEulerProduct (le_refl 1),
      constantCoeff_qEulerProduct (by norm_num : 1 ≤ 4),
      constantCoeff_qEulerProduct (by omega : 1 ≤ 2 * l)]
  rw [hmk, regularCubicOverlinedSeries, mul_comm, mul_assoc, invOfUnit_mul _ _ hc, mul_one]

/-- `a_ℓ(0) = 1` for `ℓ ≥ 1`.

Source: Pujashree Buragohain and Nipen Saikia, *Some New Congruences for l-Regular Cubic
Partitions with Odd Parts Overlined*, INTEGERS 24 (2024), Article A101, Section 1, eq. (2). -/
public theorem regularCubicOverlinedCount_zero {l : ℕ} (hl : 1 ≤ l) :
    regularCubicOverlinedCount l 0 = 1 := by
  have h := congrArg (coeff 0) (regularCubicOverlinedCount_generatingFunction hl)
  simp only [coeff_zero_eq_constantCoeff, map_mul, map_pow,
    constantCoeff_qEulerProduct (le_refl 1), constantCoeff_qEulerProduct (by norm_num : 1 ≤ 2),
    constantCoeff_qEulerProduct (by norm_num : 1 ≤ 4), constantCoeff_qEulerProduct hl,
    constantCoeff_qEulerProduct (by omega : 1 ≤ 2 * l),
    constantCoeff_qEulerProduct (by omega : 1 ≤ 4 * l), one_pow, one_mul, mul_one] at h
  simpa using h

/-- The 2-dissections
(9) `f_3 / f_1 = f_4 f_6 f_16 f_24² / (f_2² f_8 f_12 f_48) + q f_6 f_8² f_48 / (f_2² f_16 f_24)`,
(10) `f_1³ / f_3 = f_4³ / f_12 - 3q f_2² f_12³ / (f_4 f_6²)`,
(13) `f_5 / f_1 = f_8 f_20² / (f_2² f_40) + q f_4³ f_10 f_40 / (f_2³ f_8 f_20)` and
(14) `f_1 / f_5 = f_2 f_8 f_20³ / (f_4 f_10³ f_40) - q f_4² f_40 / (f_8 f_10²)`, each stated
with denominators cleared (multiplied by `f_1 f_2² f_8 f_12 f_16 f_24 f_48`,
`f_3 f_4 f_6² f_12`, `f_1 f_2³ f_8 f_20 f_40` and `f_5 f_4 f_8 f_10³ f_40` respectively).
The lemma's other identities are stated elsewhere (see the module docstring).

Source: Pujashree Buragohain and Nipen Saikia, *Some New Congruences for l-Regular Cubic
Partitions with Odd Parts Overlined*, INTEGERS 24 (2024), Article A101, Lemma 3, eqs. (9),
(10), (13), (14) (`integers-2024-A101-lem-3`). -/
public theorem_wanted f3_f5_quotients_two_dissection :
    𝔣 3 * 𝔣 2 ^ 2 * 𝔣 8 * 𝔣 12 * 𝔣 16 * 𝔣 24 * 𝔣 48 =
        𝔣 1 * (𝔣 4 * 𝔣 6 * 𝔣 16 ^ 2 * 𝔣 24 ^ 3 + X * 𝔣 6 * 𝔣 8 ^ 3 * 𝔣 12 * 𝔣 48 ^ 2) ∧
      𝔣 1 ^ 3 * 𝔣 4 * 𝔣 6 ^ 2 * 𝔣 12 =
        𝔣 3 * (𝔣 4 ^ 4 * 𝔣 6 ^ 2 - 3 * X * 𝔣 2 ^ 2 * 𝔣 12 ^ 4) ∧
      𝔣 5 * 𝔣 2 ^ 3 * 𝔣 8 * 𝔣 20 * 𝔣 40 =
        𝔣 1 * (𝔣 2 * 𝔣 8 ^ 2 * 𝔣 20 ^ 3 + X * 𝔣 4 ^ 3 * 𝔣 10 * 𝔣 40 ^ 2) ∧
      𝔣 1 * 𝔣 4 * 𝔣 8 * 𝔣 10 ^ 3 * 𝔣 40 =
        𝔣 5 * (𝔣 2 * 𝔣 8 ^ 2 * 𝔣 20 ^ 3 - X * 𝔣 4 ^ 3 * 𝔣 10 * 𝔣 40 ^ 2)

/-- For all `k, n ≥ 0`: (i) `a_{2k}(4n + 3) ≡ 0 (mod 4)` for `k > 1`;
(ii) `a_{2k+1}(4n + 2) ≡ 0 (mod 4)` for `k ≥ 1`; (iii) `a_{4k}(4n + 2) ≡ 0 (mod 4)` for
`k > 0`; (iv) `a_{4k+1}(4n + 3) ≡ 0 (mod 4)` for `k > 0`.

Source: Pujashree Buragohain and Nipen Saikia, *Some New Congruences for l-Regular Cubic
Partitions with Odd Parts Overlined*, INTEGERS 24 (2024), Article A101, Theorem 5,
eqs. (17)–(20) (`integers-2024-A101-thm-5`). -/
public theorem_wanted regularCubicOverlinedCount_mod_four (k n : ℕ) :
    (1 < k → (4 : ℤ) ∣ regularCubicOverlinedCount (2 * k) (4 * n + 3)) ∧
      (1 ≤ k → (4 : ℤ) ∣ regularCubicOverlinedCount (2 * k + 1) (4 * n + 2)) ∧
      (0 < k → (4 : ℤ) ∣ regularCubicOverlinedCount (4 * k) (4 * n + 2)) ∧
      (0 < k → (4 : ℤ) ∣ regularCubicOverlinedCount (4 * k + 1) (4 * n + 3))

/-- For a prime `p ≥ 5` with Legendre symbol `(-6/p) = -1`, all `δ, n ≥ 0` and
`1 ≤ t ≤ p - 1`: `a_3(8p^{2δ} n + (10p^{2δ} - 1)/3) ≡ [qⁿ] 6 f_4 f_6 (mod 12)` and
`a_3(8p^{2δ+2} n + 8p^{2δ+1} t + (10p^{2δ+2} - 1)/3) ≡ 0 (mod 12)`. The divisions are
exact.

Source: Pujashree Buragohain and Nipen Saikia, *Some New Congruences for l-Regular Cubic
Partitions with Odd Parts Overlined*, INTEGERS 24 (2024), Article A101, Theorem 6,
eqs. (26), (27) (`integers-2024-A101-thm-6`). -/
public theorem_wanted regularCubicOverlinedCount_three_prime_mod_twelve (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p) (hleg : legendreSym p (-6) = -1) (δ : ℕ) :
    (∀ n : ℕ, regularCubicOverlinedCount 3 (8 * p ^ (2 * δ) * n + (10 * p ^ (2 * δ) - 1) / 3) ≡
        6 * coeff n (𝔣 4 * 𝔣 6) [ZMOD 12]) ∧
      ∀ n t : ℕ, 1 ≤ t → t ≤ p - 1 →
        regularCubicOverlinedCount 3 (8 * p ^ (2 * δ + 2) * n + 8 * p ^ (2 * δ + 1) * t +
          (10 * p ^ (2 * δ + 2) - 1) / 3) ≡ 0 [ZMOD 12]

/-- For all `n ≥ 0`: `a_3(8n + 5) ≡ 0 (mod 18)`, `a_3(16n + 11) ≡ 0 (mod 12)` and
`a_3(16n + 15) ≡ 0 (mod 12)`.

Source: Pujashree Buragohain and Nipen Saikia, *Some New Congruences for l-Regular Cubic
Partitions with Odd Parts Overlined*, INTEGERS 24 (2024), Article A101, Corollary 1,
eqs. (39)–(41) (`integers-2024-A101-cor-1`). -/
public theorem_wanted regularCubicOverlinedCount_three_mod_eighteen_twelve (n : ℕ) :
    (18 : ℤ) ∣ regularCubicOverlinedCount 3 (8 * n + 5) ∧
      (12 : ℤ) ∣ regularCubicOverlinedCount 3 (16 * n + 11) ∧
      (12 : ℤ) ∣ regularCubicOverlinedCount 3 (16 * n + 15)

/-- For a prime `p ≥ 5` with `(-3/p) = -1`, all `δ, n ≥ 0` and `1 ≤ t ≤ p - 1`:
`a_3(8p^{2δ} n + (4p^{2δ} - 1)/3) ≡ [qⁿ] 2 f_1 f_3 (mod 6)` and
`a_3(8p^{2δ+2} n + 8p^{2δ+1} t + (4p^{2δ+2} - 1)/3) ≡ 0 (mod 6)`. The divisions are exact.

Source: Pujashree Buragohain and Nipen Saikia, *Some New Congruences for l-Regular Cubic
Partitions with Odd Parts Overlined*, INTEGERS 24 (2024), Article A101, Theorem 7, eq. (46)
and the unnumbered congruence after it (`integers-2024-A101-thm-7`). -/
public theorem_wanted regularCubicOverlinedCount_three_prime_mod_six (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p) (hleg : legendreSym p (-3) = -1) (δ : ℕ) :
    (∀ n : ℕ, regularCubicOverlinedCount 3 (8 * p ^ (2 * δ) * n + (4 * p ^ (2 * δ) - 1) / 3) ≡
        2 * coeff n (𝔣 1 * 𝔣 3) [ZMOD 6]) ∧
      ∀ n t : ℕ, 1 ≤ t → t ≤ p - 1 →
        regularCubicOverlinedCount 3 (8 * p ^ (2 * δ + 2) * n + 8 * p ^ (2 * δ + 1) * t +
          (4 * p ^ (2 * δ + 2) - 1) / 3) ≡ 0 [ZMOD 6]

/-- For a prime `p ≥ 5` with `(-2/p) = -1`, all `δ, n ≥ 0` and `1 ≤ t ≤ p - 1`:
`a_4(4p^{2δ} n + (3p^{2δ} - 1)/2) ≡ [qⁿ] 2 f_1 f_8 (mod 4)` and
`a_4(4p^{2δ+2} n + 4p^{2δ+1} t + (3p^{2δ+2} - 1)/2) ≡ 0 (mod 4)`. The divisions are exact.

Source: Pujashree Buragohain and Nipen Saikia, *Some New Congruences for l-Regular Cubic
Partitions with Odd Parts Overlined*, INTEGERS 24 (2024), Article A101, Theorem 8, eq. (49)
and the unnumbered congruence after it (`integers-2024-A101-thm-8`). -/
public theorem_wanted regularCubicOverlinedCount_four_prime_mod_four (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p) (hleg : legendreSym p (-2) = -1) (δ : ℕ) :
    (∀ n : ℕ, regularCubicOverlinedCount 4 (4 * p ^ (2 * δ) * n + (3 * p ^ (2 * δ) - 1) / 2) ≡
        2 * coeff n (𝔣 1 * 𝔣 8) [ZMOD 4]) ∧
      ∀ n t : ℕ, 1 ≤ t → t ≤ p - 1 →
        regularCubicOverlinedCount 4 (4 * p ^ (2 * δ + 2) * n + 4 * p ^ (2 * δ + 1) * t +
          (3 * p ^ (2 * δ + 2) - 1) / 2) ≡ 0 [ZMOD 4]

/-- For all `n ≥ 0`: `a_4(4n + 3) ≡ 0 (mod 8)`, `a_4(28n + 4j + 3) ≡ 0 (mod 56)` for
`j = 1, …, 6`, and `a_4(36n + 19) ≡ 0 (mod 24)`.

Source: Pujashree Buragohain and Nipen Saikia, *Some New Congruences for l-Regular Cubic
Partitions with Odd Parts Overlined*, INTEGERS 24 (2024), Article A101, Corollary 2,
eqs. (55)–(57) (`integers-2024-A101-cor-2`). -/
public theorem_wanted regularCubicOverlinedCount_four_mod_eight_fiftySix_twentyFour (n : ℕ) :
    (8 : ℤ) ∣ regularCubicOverlinedCount 4 (4 * n + 3) ∧
      (∀ j ∈ Finset.Icc 1 6, (56 : ℤ) ∣ regularCubicOverlinedCount 4 (28 * n + 4 * j + 3)) ∧
      (24 : ℤ) ∣ regularCubicOverlinedCount 4 (36 * n + 19)

/-- For a prime `p ≥ 5` with `(-3/p) = -1`, `s = (±p - 1)/6` (that is, `(p - 1)/6` if
`p ≡ 1 (mod 6)` and `(-p - 1)/6` if `p ≡ -1 (mod 6)`), all `δ, n ≥ 0` and
`1 ≤ t ≤ p - 1`:
(64) `a_5(10p^{2δ} n + (5p^{2δ} - 2)/3) ≡ [qⁿ] 2(-1)^{δs} f_1 ψ(q) (mod 8)`, where
`f_1 ψ(q) = f_2²`;
(65) `a_5(10p^{2δ+2} n + 10p^{2δ+1} t + (5p^{2δ+2} - 2)/3) ≡ 0 (mod 8)`;
(66) `∑ a_5(40p^{2δ} n + (65p^{2δ} - 2)/3) qⁿ ≡ 4(-1)^{δs} f_1 ψ(q⁴) (mod 8)`, with
`ψ(q⁴) = f_8² / f_4`, stated after multiplying both sides by `f_4`;
(67) `a_5(40p^{2δ+2} n + 40p^{2δ+1} t + (65p^{2δ+2} - 2)/3) ≡ 0 (mod 8)`.
The divisions are exact.

Source: Pujashree Buragohain and Nipen Saikia, *Some New Congruences for l-Regular Cubic
Partitions with Odd Parts Overlined*, INTEGERS 24 (2024), Article A101, Theorem 9,
eqs. (64)–(67) (`integers-2024-A101-thm-9`). -/
public theorem_wanted regularCubicOverlinedCount_five_prime_mod_eight (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p) (hleg : legendreSym p (-3) = -1)
    (s : ℤ) (hs : s = if p % 6 = 1 then ((p : ℤ) - 1) / 6 else (-(p : ℤ) - 1) / 6) (δ : ℕ) :
    (∀ n : ℕ, regularCubicOverlinedCount 5 (10 * p ^ (2 * δ) * n + (5 * p ^ (2 * δ) - 2) / 3) ≡
        2 * (-1) ^ ((δ : ℤ) * s).natAbs * coeff n (𝔣 2 ^ 2) [ZMOD 8]) ∧
      (∀ n t : ℕ, 1 ≤ t → t ≤ p - 1 →
        regularCubicOverlinedCount 5 (10 * p ^ (2 * δ + 2) * n + 10 * p ^ (2 * δ + 1) * t +
          (5 * p ^ (2 * δ + 2) - 2) / 3) ≡ 0 [ZMOD 8]) ∧
      (∀ n : ℕ, coeff n (𝔣 4 * PowerSeries.mk fun m =>
          regularCubicOverlinedCount 5 (40 * p ^ (2 * δ) * m + (65 * p ^ (2 * δ) - 2) / 3)) ≡
        4 * (-1) ^ ((δ : ℤ) * s).natAbs * coeff n (𝔣 1 * 𝔣 8 ^ 2) [ZMOD 8]) ∧
      ∀ n t : ℕ, 1 ≤ t → t ≤ p - 1 →
        regularCubicOverlinedCount 5 (40 * p ^ (2 * δ + 2) * n + 40 * p ^ (2 * δ + 1) * t +
          (65 * p ^ (2 * δ + 2) - 2) / 3) ≡ 0 [ZMOD 8]

/-- For all `n ≥ 0`: `a_5(8n + 7) ≡ 0 (mod 16)` and `a_5(20n + 2j + 1) ≡ 0 (mod 8)` for
`j = 1, …, 9`.

Source: Pujashree Buragohain and Nipen Saikia, *Some New Congruences for l-Regular Cubic
Partitions with Odd Parts Overlined*, INTEGERS 24 (2024), Article A101, Corollary 3,
eqs. (76), (77) (`integers-2024-A101-cor-3`). -/
public theorem_wanted regularCubicOverlinedCount_five_mod_sixteen_eight (n : ℕ) :
    (16 : ℤ) ∣ regularCubicOverlinedCount 5 (8 * n + 7) ∧
      ∀ j ∈ Finset.Icc 1 9, (8 : ℤ) ∣ regularCubicOverlinedCount 5 (20 * n + 2 * j + 1)

/-- For a prime `p ≥ 5` with `(-15/p) = -1`, `s = (±p - 1)/6` as in Theorem 9, all
`δ, n ≥ 0` and `1 ≤ t ≤ p - 1`:
(80) `∑ a_5(16p^{2δ+2} n + (122p^{2δ+2} - 2)/3) qⁿ ≡ 2(-1)^{(δ+1)s} f_1 ψ(q^{20}) (mod 4)`,
with `ψ(q^{20}) = f_40² / f_20`, stated after multiplying both sides by `f_20`;
(81) `a_5(16p^{2δ+2} n + 16p^{2δ+1} t + (122p^{2δ+2} - 2)/3) ≡ 0 (mod 4)`.
The divisions are exact.

Source: Pujashree Buragohain and Nipen Saikia, *Some New Congruences for l-Regular Cubic
Partitions with Odd Parts Overlined*, INTEGERS 24 (2024), Article A101, Theorem 10,
eqs. (80), (81) (`integers-2024-A101-thm-10`). -/
public theorem_wanted regularCubicOverlinedCount_five_prime_mod_four (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p) (hleg : legendreSym p (-15) = -1)
    (s : ℤ) (hs : s = if p % 6 = 1 then ((p : ℤ) - 1) / 6 else (-(p : ℤ) - 1) / 6) (δ : ℕ) :
    (∀ n : ℕ, coeff n (𝔣 20 * PowerSeries.mk fun m =>
          regularCubicOverlinedCount 5
            (16 * p ^ (2 * δ + 2) * m + (122 * p ^ (2 * δ + 2) - 2) / 3)) ≡
        2 * (-1) ^ (((δ : ℤ) + 1) * s).natAbs * coeff n (𝔣 1 * 𝔣 40 ^ 2) [ZMOD 4]) ∧
      ∀ n t : ℕ, 1 ≤ t → t ≤ p - 1 →
        regularCubicOverlinedCount 5 (16 * p ^ (2 * δ + 2) * n + 16 * p ^ (2 * δ + 1) * t +
          (122 * p ^ (2 * δ + 2) - 2) / 3) ≡ 0 [ZMOD 4]

/-- For a prime `p ≥ 5` with `(-3/p) = -1`, `s = (±p - 1)/6` as in Theorem 9, all
`δ, n ≥ 0` and `1 ≤ t ≤ p - 1`:
(93) `∑ a_8(4p^{2δ} n + (13p^{2δ} - 7)/6) qⁿ ≡ 2(-1)^{δs} f_1 ψ(q⁴) (mod 4)`, with
`ψ(q⁴) = f_8² / f_4`, stated after multiplying both sides by `f_4`;
(94) `a_8(4p^{2δ+2} n + 4p^{2δ+1} t + (13p^{2δ+2} - 7)/6) ≡ 0 (mod 4)`;
(95) `∑ a_8(4p^{2δ} n + (19p^{2δ} - 7)/6) qⁿ ≡ 4(-1)^{δs} ψ(q) f_16 (mod 8)`, with
`ψ(q) = f_2² / f_1`, stated after multiplying both sides by `f_1`;
(96) `a_8(4p^{2δ+2} n + 4p^{2δ+1} t + (19p^{2δ+2} - 7)/6) ≡ 0 (mod 8)`.
The divisions are exact.

Source: Pujashree Buragohain and Nipen Saikia, *Some New Congruences for l-Regular Cubic
Partitions with Odd Parts Overlined*, INTEGERS 24 (2024), Article A101, Theorem 11,
eqs. (93)–(96) (`integers-2024-A101-thm-11`). -/
public theorem_wanted regularCubicOverlinedCount_eight_prime_mod_four_eight (p : ℕ)
    [Fact p.Prime] (hp : 5 ≤ p) (hleg : legendreSym p (-3) = -1)
    (s : ℤ) (hs : s = if p % 6 = 1 then ((p : ℤ) - 1) / 6 else (-(p : ℤ) - 1) / 6) (δ : ℕ) :
    (∀ n : ℕ, coeff n (𝔣 4 * PowerSeries.mk fun m =>
          regularCubicOverlinedCount 8 (4 * p ^ (2 * δ) * m + (13 * p ^ (2 * δ) - 7) / 6)) ≡
        2 * (-1) ^ ((δ : ℤ) * s).natAbs * coeff n (𝔣 1 * 𝔣 8 ^ 2) [ZMOD 4]) ∧
      (∀ n t : ℕ, 1 ≤ t → t ≤ p - 1 →
        regularCubicOverlinedCount 8 (4 * p ^ (2 * δ + 2) * n + 4 * p ^ (2 * δ + 1) * t +
          (13 * p ^ (2 * δ + 2) - 7) / 6) ≡ 0 [ZMOD 4]) ∧
      (∀ n : ℕ, coeff n (𝔣 1 * PowerSeries.mk fun m =>
          regularCubicOverlinedCount 8 (4 * p ^ (2 * δ) * m + (19 * p ^ (2 * δ) - 7) / 6)) ≡
        4 * (-1) ^ ((δ : ℤ) * s).natAbs * coeff n (𝔣 2 ^ 2 * 𝔣 16) [ZMOD 8]) ∧
      ∀ n t : ℕ, 1 ≤ t → t ≤ p - 1 →
        regularCubicOverlinedCount 8 (4 * p ^ (2 * δ + 2) * n + 4 * p ^ (2 * δ + 1) * t +
          (19 * p ^ (2 * δ + 2) - 7) / 6) ≡ 0 [ZMOD 8]

/-- For a prime `p ≥ 5` with `(-6/p) = -1`, `s = (±p - 1)/6` as in Theorem 9, all
`δ, n ≥ 0` and `1 ≤ t ≤ p - 1`:
(105) `∑ a_8(4p^{2δ} n + (25p^{2δ} - 7)/6) qⁿ ≡ 8(-1)^{δs} f_1 ψ(q⁸) (mod 16)`, with
`ψ(q⁸) = f_16² / f_8`, stated after multiplying both sides by `f_8`;
(106) `a_8(4p^{2δ+2} n + 4p^{2δ+1} t + (25p^{2δ+2} - 7)/6) ≡ 0 (mod 16)`.
The divisions are exact.

Source: Pujashree Buragohain and Nipen Saikia, *Some New Congruences for l-Regular Cubic
Partitions with Odd Parts Overlined*, INTEGERS 24 (2024), Article A101, Theorem 12,
eqs. (105), (106) (`integers-2024-A101-thm-12`). -/
public theorem_wanted regularCubicOverlinedCount_eight_prime_mod_sixteen (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p) (hleg : legendreSym p (-6) = -1)
    (s : ℤ) (hs : s = if p % 6 = 1 then ((p : ℤ) - 1) / 6 else (-(p : ℤ) - 1) / 6) (δ : ℕ) :
    (∀ n : ℕ, coeff n (𝔣 8 * PowerSeries.mk fun m =>
          regularCubicOverlinedCount 8 (4 * p ^ (2 * δ) * m + (25 * p ^ (2 * δ) - 7) / 6)) ≡
        8 * (-1) ^ ((δ : ℤ) * s).natAbs * coeff n (𝔣 1 * 𝔣 16 ^ 2) [ZMOD 16]) ∧
      ∀ n t : ℕ, 1 ≤ t → t ≤ p - 1 →
        regularCubicOverlinedCount 8 (4 * p ^ (2 * δ + 2) * n + 4 * p ^ (2 * δ + 1) * t +
          (25 * p ^ (2 * δ + 2) - 7) / 6) ≡ 0 [ZMOD 16]

/-- For a prime `p ≥ 5` with `(-2/p) = -1`, all `δ, n ≥ 0` and `1 ≤ t ≤ p - 1`:
`a_9(8p^{2δ} n + (19p^{2δ} - 4)/3) ≡ [qⁿ] 2 f_1 f_18 (mod 4)` and
`a_9(8p^{2δ+2} n + 8p^{2δ+1} t + (19p^{2δ+2} - 4)/3) ≡ 0 (mod 4)`. The divisions are exact.

Source: Pujashree Buragohain and Nipen Saikia, *Some New Congruences for l-Regular Cubic
Partitions with Odd Parts Overlined*, INTEGERS 24 (2024), Article A101, Theorem 13, eq. (110)
and the unnumbered congruence after it (`integers-2024-A101-thm-13`). -/
public theorem_wanted regularCubicOverlinedCount_nine_prime_mod_four (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p) (hleg : legendreSym p (-2) = -1) (δ : ℕ) :
    (∀ n : ℕ, regularCubicOverlinedCount 9 (8 * p ^ (2 * δ) * n + (19 * p ^ (2 * δ) - 4) / 3) ≡
        2 * coeff n (𝔣 1 * 𝔣 18) [ZMOD 4]) ∧
      ∀ n t : ℕ, 1 ≤ t → t ≤ p - 1 →
        regularCubicOverlinedCount 9 (8 * p ^ (2 * δ + 2) * n + 8 * p ^ (2 * δ + 1) * t +
          (19 * p ^ (2 * δ + 2) - 4) / 3) ≡ 0 [ZMOD 4]

/-- For all `n ≥ 0`, `a_9(4n + 3) ≡ 0 (mod 8)`.

Source: Pujashree Buragohain and Nipen Saikia, *Some New Congruences for l-Regular Cubic
Partitions with Odd Parts Overlined*, INTEGERS 24 (2024), Article A101, Corollary 4,
eq. (118) (`integers-2024-A101-cor-4`). -/
public theorem_wanted regularCubicOverlinedCount_nine_four_mul_add_three (n : ℕ) :
    (8 : ℤ) ∣ regularCubicOverlinedCount 9 (4 * n + 3)

/-- For a prime `p ≥ 5` with `(-2/p) = -1`, all `δ, n ≥ 0` and `1 ≤ t ≤ p - 1`:
`a_16(4p^{2δ} n + (11p^{2δ} - 5)/2) ≡ [qⁿ] 8 f_1 f_32 (mod 16)` and
`a_16(4p^{2δ+2} n + 4p^{2δ+1} t + (11p^{2δ+2} - 5)/2) ≡ 0 (mod 16)`. The divisions are
exact.

Source: Pujashree Buragohain and Nipen Saikia, *Some New Congruences for l-Regular Cubic
Partitions with Odd Parts Overlined*, INTEGERS 24 (2024), Article A101, Theorem 14, eq. (119)
and the unnumbered congruence after it (`integers-2024-A101-thm-14`). -/
public theorem_wanted regularCubicOverlinedCount_sixteen_prime_mod_sixteen (p : ℕ)
    [Fact p.Prime] (hp : 5 ≤ p) (hleg : legendreSym p (-2) = -1) (δ : ℕ) :
    (∀ n : ℕ, regularCubicOverlinedCount 16 (4 * p ^ (2 * δ) * n + (11 * p ^ (2 * δ) - 5) / 2) ≡
        8 * coeff n (𝔣 1 * 𝔣 32) [ZMOD 16]) ∧
      ∀ n t : ℕ, 1 ≤ t → t ≤ p - 1 →
        regularCubicOverlinedCount 16 (4 * p ^ (2 * δ + 2) * n + 4 * p ^ (2 * δ + 1) * t +
          (11 * p ^ (2 * δ + 2) - 5) / 2) ≡ 0 [ZMOD 16]

end

end MetaMathlibExt
