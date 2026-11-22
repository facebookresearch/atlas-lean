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
# Congruences for `[j, k]`-overpartition pairs with even parts distinct (statements)

Statements from Adam Paksok and Nipen Saikia, *New Congruences for `[j, k]`-Overpartition Pairs
with Even Parts Distinct*, INTEGERS 26 (2026), Article A118. `bped_{j,k}(n)` is
`overpartitionPairEvenDistinct j k n`, the coefficient of `q^n` in the paper's generating
function (2). The paper's quotients `(… - 1)/2` are natural-number divisions of even numbers.
-/

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace MetaMathlibExt

@[expose] public section

/-- The generating function `(q^4; q^4)_∞^2 (-q^j; q^k)_∞^2 / (q; q)_∞^2` of `[j, k]`-overpartition
pairs with even parts distinct, as an integer power series: `f_4^2 (∏_{i ≥ 0} (1 + q^{j+ki}))^2`
times the inverse of `f_1^2` (constant coefficient `1`), with `f_k = qEulerProduct k` (used for
`k ≥ j ≥ 1`).

Source: Adam Paksok and Nipen Saikia, *New Congruences for `[j, k]`-Overpartition Pairs with Even
Parts Distinct*, INTEGERS 26 (2026), Article A118, Section 1, Equation (2). -/
public noncomputable def overpartitionPairEvenDistinctGF (j k : ℕ) : ℤ⟦X⟧ :=
  qEulerProduct 4 ^ 2 * (∏' i : ℕ, (1 + X ^ (j + k * i))) ^ 2 *
    PowerSeries.invOfUnit (qEulerProduct 1 ^ 2) 1

/-- `bped_{j,k}(n)`, the number of `[j, k]`-overpartition pairs of `n` with even parts distinct
(the first occurrence of each distinct part congruent to `j` modulo `k` may be overlined): the
coefficient of `q^n` in `overpartitionPairEvenDistinctGF j k`.

Source: Adam Paksok and Nipen Saikia, *New Congruences for `[j, k]`-Overpartition Pairs with Even
Parts Distinct*, INTEGERS 26 (2026), Article A118, Section 1, Equation (2). -/
public noncomputable def overpartitionPairEvenDistinct (j k n : ℕ) : ℤ :=
  coeff n (overpartitionPairEvenDistinctGF j k)

/-- The generating function identity (2) in cleared form:
`(∑ bped_{j,k}(n) q^n) · (q; q)_∞^2 = (q^4; q^4)_∞^2 (-q^j; q^k)_∞^2`.

Source: Adam Paksok and Nipen Saikia, *New Congruences for `[j, k]`-Overpartition Pairs with Even
Parts Distinct*, INTEGERS 26 (2026), Article A118, Section 1, Equation (2). -/
public theorem overpartitionPairEvenDistinctGF_mul_qEulerProduct_sq (j k : ℕ) :
    overpartitionPairEvenDistinctGF j k * qEulerProduct 1 ^ 2 =
      qEulerProduct 4 ^ 2 * (∏' i : ℕ, (1 + X ^ (j + k * i))) ^ 2 := by
  have h : constantCoeff (qEulerProduct 1 ^ 2) = ((1 : ℤˣ) : ℤ) := by
    rw [map_pow, constantCoeff_qEulerProduct le_rfl]
    simp
  rw [overpartitionPairEvenDistinctGF, mul_assoc, PowerSeries.invOfUnit_mul _ _ h, mul_one]

/-- `bped_{j,k}(0) = 1` for `j, k ≥ 1` (the pair of empty overpartitions).

Source: Adam Paksok and Nipen Saikia, *New Congruences for `[j, k]`-Overpartition Pairs with Even
Parts Distinct*, INTEGERS 26 (2026), Article A118, Section 1, Equation (2). -/
public theorem overpartitionPairEvenDistinct_zero (j k : ℕ) (hj : 1 ≤ j) (hk : 1 ≤ k) :
    overpartitionPairEvenDistinct j k 0 = 1 := by
  have hmul : Multipliable fun i : ℕ => (1 : ℤ⟦X⟧) + X ^ (j + k * i) := by
    apply WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top
    refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr fun n => Filter.eventually_atTop.mpr ⟨n, ?_⟩
    intro m hm
    rw [order_X_pow]
    norm_cast
    nlinarith
  have hD : constantCoeff (∏' i : ℕ, ((1 : ℤ⟦X⟧) + X ^ (j + k * i))) = 1 := by
    rw [hmul.map_tprod _ (WithPiTopology.continuous_constantCoeff ℤ)]
    have h1 : ∀ i : ℕ, constantCoeff ((1 : ℤ⟦X⟧) + X ^ (j + k * i)) = 1 := fun i => by
      have : j + k * i ≠ 0 := by omega
      simp [zero_pow this]
    simp [h1]
  have hinv : constantCoeff (PowerSeries.invOfUnit (qEulerProduct 1 ^ 2) (1 : ℤˣ)) = 1 := by
    simp
  rw [overpartitionPairEvenDistinct, coeff_zero_eq_constantCoeff_apply,
    overpartitionPairEvenDistinctGF, map_mul, map_mul, map_pow, map_pow, hD,
    constantCoeff_qEulerProduct (by norm_num), hinv]
  simp

/-- For a prime `p > 5` with `(-6/p) = -1` and all `k, m, α, β ≥ 0` with `p ∤ m`:
`bped_{3,3}(4·3^{4α+3}·5^{2β}·p^{2k+1} m + (7·3^{4α+2}·5^{2β}·p^{2k+2} - 1)/2) ≡ 0 (mod 16)` (6) and
`bped_{3,3}(12·5^{2β}·p^{2k+1} m + (7·5^{2β}·p^{2k+2} - 1)/2) ≡ 0 (mod 8)` (7).
The paper prints `p^{2α+2}` in the second summands; the proof substitutes
`n = p^{2k+1} m + 7(p^{2k+2} - 1)/24`, which gives `p^{2k+2}`, and the printed exponent fails:
`p = 13, k = 1, α = β = 0, m = 2` in (7) gives `bped_{3,3}(53319) ≡ 4 (mod 8)`.

Source: Adam Paksok and Nipen Saikia, *New Congruences for `[j, k]`-Overpartition Pairs with Even
Parts Distinct*, INTEGERS 26 (2026), Article A118, Theorem 1
(`integers-2026-A118-thm-1`). -/
public theorem_wanted overpartitionPairEvenDistinct_three_three_congr_neg_six
    (p : ℕ) [Fact p.Prime] (hp : 5 < p) (hleg : legendreSym p (-6) = -1)
    (k m α β : ℕ) (hm : ¬ p ∣ m) :
    (16 : ℤ) ∣ overpartitionPairEvenDistinct 3 3
        (4 * 3 ^ (4 * α + 3) * 5 ^ (2 * β) * p ^ (2 * k + 1) * m +
          (7 * 3 ^ (4 * α + 2) * 5 ^ (2 * β) * p ^ (2 * k + 2) - 1) / 2) ∧
      (8 : ℤ) ∣ overpartitionPairEvenDistinct 3 3
        (12 * 5 ^ (2 * β) * p ^ (2 * k + 1) * m + (7 * 5 ^ (2 * β) * p ^ (2 * k + 2) - 1) / 2)

/-- For a prime `p ≥ 5` with `(-2/p) = -1` and all `k, m, α, β ≥ 0` with `p ∤ m`:
`bped_{3,3}(4·3^{4α+3}·5^{2β}·p^{2k+1} m + (11·3^{4α+2}·5^{2β}·p^{2k+2} - 1)/2) ≡ 0 (mod 16)`
(10), `bped_{3,3}(12·5^{2β}·p^{2k+1} m + (11·5^{2β}·p^{2k+2} - 1)/2) ≡ 0 (mod 4)` (11),
`bped_{3,6}(3^{4α+2}·5^{2β}·p^{2k+1}(24m + 11p)) ≡ 0 (mod 32)` (12) and
`bped_{3,6}(3·5^{2β}·p^{2k+1}(24m + 11p)) ≡ 0 (mod 32)` (13).
The paper prints `p^{2α+2}` in (10) and (11); the proof's substitution gives `p^{2k+2}`, and the
printed exponent fails: `p = 5, k = 1, α = β = 0, m = 1` gives `bped_{3,3}(14737) ≡ 8 (mod 16)` in
(10) and `bped_{3,3}(1637) ≡ 2 (mod 4)` in (11).

Source: Adam Paksok and Nipen Saikia, *New Congruences for `[j, k]`-Overpartition Pairs with Even
Parts Distinct*, INTEGERS 26 (2026), Article A118, Theorem 2
(`integers-2026-A118-thm-2`). -/
public theorem_wanted overpartitionPairEvenDistinct_congr_neg_two_eleven
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (hleg : legendreSym p (-2) = -1)
    (k m α β : ℕ) (hm : ¬ p ∣ m) :
    (16 : ℤ) ∣ overpartitionPairEvenDistinct 3 3
        (4 * 3 ^ (4 * α + 3) * 5 ^ (2 * β) * p ^ (2 * k + 1) * m +
          (11 * 3 ^ (4 * α + 2) * 5 ^ (2 * β) * p ^ (2 * k + 2) - 1) / 2) ∧
      (4 : ℤ) ∣ overpartitionPairEvenDistinct 3 3
        (12 * 5 ^ (2 * β) * p ^ (2 * k + 1) * m + (11 * 5 ^ (2 * β) * p ^ (2 * k + 2) - 1) / 2) ∧
      (32 : ℤ) ∣ overpartitionPairEvenDistinct 3 6
        (3 ^ (4 * α + 2) * 5 ^ (2 * β) * p ^ (2 * k + 1) * (24 * m + 11 * p)) ∧
      (32 : ℤ) ∣ overpartitionPairEvenDistinct 3 6
        (3 * 5 ^ (2 * β) * p ^ (2 * k + 1) * (24 * m + 11 * p))

/-- For a prime `p ≥ 5` with `(-2/p) = -1` and all `k, m, α, β ≥ 0` with `p ∤ m`:
`bped_{3,3}(4·3^{4α+3}·5^{2β}·p^{2k+1} m + (19·3^{4α+2}·5^{2β}·p^{2k+2} - 1)/2) ≡ 0 (mod 16)`
(16), `bped_{3,3}(12·5^{2β}·p^{2k+1} m + (19·5^{2β}·p^{2k+2} - 1)/2) ≡ 0 (mod 8)` (17),
`bped_{3,6}(3^{4α+2}·5^{2β}·p^{2k+1}(24m + 19p)) ≡ 0 (mod 32)` (18) and
`bped_{3,6}(3·5^{2β}·p^{2k+1}(24m + 19p)) ≡ 0 (mod 32)` (19).
The paper prints `p^{2α+2}` in (16) and (17); the proof's substitution gives `p^{2k+2}`, and the
printed exponent fails: `p = 5, k = 1, α = β = 0, m = 1` gives `bped_{3,3}(15637) ≡ 8 (mod 16)` in
(16) and `bped_{3,3}(1737) ≡ 4 (mod 8)` in (17).

Source: Adam Paksok and Nipen Saikia, *New Congruences for `[j, k]`-Overpartition Pairs with Even
Parts Distinct*, INTEGERS 26 (2026), Article A118, Theorem 3
(`integers-2026-A118-thm-3`). -/
public theorem_wanted overpartitionPairEvenDistinct_congr_neg_two_nineteen
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (hleg : legendreSym p (-2) = -1)
    (k m α β : ℕ) (hm : ¬ p ∣ m) :
    (16 : ℤ) ∣ overpartitionPairEvenDistinct 3 3
        (4 * 3 ^ (4 * α + 3) * 5 ^ (2 * β) * p ^ (2 * k + 1) * m +
          (19 * 3 ^ (4 * α + 2) * 5 ^ (2 * β) * p ^ (2 * k + 2) - 1) / 2) ∧
      (8 : ℤ) ∣ overpartitionPairEvenDistinct 3 3
        (12 * 5 ^ (2 * β) * p ^ (2 * k + 1) * m + (19 * 5 ^ (2 * β) * p ^ (2 * k + 2) - 1) / 2) ∧
      (32 : ℤ) ∣ overpartitionPairEvenDistinct 3 6
        (3 ^ (4 * α + 2) * 5 ^ (2 * β) * p ^ (2 * k + 1) * (24 * m + 19 * p)) ∧
      (32 : ℤ) ∣ overpartitionPairEvenDistinct 3 6
        (3 * 5 ^ (2 * β) * p ^ (2 * k + 1) * (24 * m + 19 * p))

/-- For a prime `p ≥ 5` with `(-1/p) = -1` and all `k, m, α, γ ≥ 0` with `p ∤ m`:
`bped_{3,3}(4·3^{4α+2}·7^{2γ}·p^{2k+1} m + (5·3^{4α+1}·7^{2γ}·p^{2k+2} - 1)/2) ≡ 0 (mod 8)` (22),
`bped_{3,6}(3^{4α+2}·7^{2γ}·p^{2k+1}(24m + 5p)) ≡ 0 (mod 16)` (23) and
`bped_{3,6}(3·7^{2γ}·p^{2k+1}(24m + 5p)) ≡ 0 (mod 16)` (24).
Deviations: the paper allows `p ≥ 3`, but the proof needs `p ∤ 24m + 5p`, which fails for `p = 3`,
and all three congruences fail there (`k = α = γ = 0, m = 1`: `bped_{3,3}(175) ≡ 4 (mod 8)`,
`bped_{3,6}(1053) ≡ 8 (mod 16)`, `bped_{3,6}(351) ≡ 8 (mod 16)`), so `p ≥ 5` is assumed; the paper
prints `p^{2α+2}` in (22), the proof's substitution gives `p^{2k+2}`, and the printed exponent
fails: `p = 7, k = 1, α = γ = 0, m = 1` gives `bped_{3,3}(12715) ≡ 4 (mod 8)`.

Source: Adam Paksok and Nipen Saikia, *New Congruences for `[j, k]`-Overpartition Pairs with Even
Parts Distinct*, INTEGERS 26 (2026), Article A118, Theorem 4
(`integers-2026-A118-thm-4`). -/
public theorem_wanted overpartitionPairEvenDistinct_congr_neg_one_five
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (hleg : legendreSym p (-1) = -1)
    (k m α γ : ℕ) (hm : ¬ p ∣ m) :
    (8 : ℤ) ∣ overpartitionPairEvenDistinct 3 3
        (4 * 3 ^ (4 * α + 2) * 7 ^ (2 * γ) * p ^ (2 * k + 1) * m +
          (5 * 3 ^ (4 * α + 1) * 7 ^ (2 * γ) * p ^ (2 * k + 2) - 1) / 2) ∧
      (16 : ℤ) ∣ overpartitionPairEvenDistinct 3 6
        (3 ^ (4 * α + 2) * 7 ^ (2 * γ) * p ^ (2 * k + 1) * (24 * m + 5 * p)) ∧
      (16 : ℤ) ∣ overpartitionPairEvenDistinct 3 6
        (3 * 7 ^ (2 * γ) * p ^ (2 * k + 1) * (24 * m + 5 * p))

/-- For a prime `p ≥ 5` with `(-3/p) = -1` and all `k, m, α, β ≥ 0` with `p ∤ m`:
`bped_{3,3}(4·3^{4α+2}·5^{2β}·p^{2k+1} m + (13·3^{4α+1}·5^{2β}·p^{2k+2} - 1)/2) ≡ 0 (mod 8)`
(27), `bped_{3,6}(3^{4α+2}·5^{2β}·p^{2k+1}(24m + 13p)) ≡ 0 (mod 16)` (28) and
`bped_{3,6}(3·5^{2β}·p^{2k+1}(24m + 13p)) ≡ 0 (mod 16)` (29).
The paper prints `p^{2α+2}` in (27); the proof's substitution gives `p^{2k+2}`, and the printed
exponent fails: `p = 5, k = 1, α = β = 0, m = 3` gives `bped_{3,3}(13987) ≡ 4 (mod 8)`.

Source: Adam Paksok and Nipen Saikia, *New Congruences for `[j, k]`-Overpartition Pairs with Even
Parts Distinct*, INTEGERS 26 (2026), Article A118, Theorem 5
(`integers-2026-A118-thm-5`). -/
public theorem_wanted overpartitionPairEvenDistinct_congr_neg_three_thirteen
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (hleg : legendreSym p (-3) = -1)
    (k m α β : ℕ) (hm : ¬ p ∣ m) :
    (8 : ℤ) ∣ overpartitionPairEvenDistinct 3 3
        (4 * 3 ^ (4 * α + 2) * 5 ^ (2 * β) * p ^ (2 * k + 1) * m +
          (13 * 3 ^ (4 * α + 1) * 5 ^ (2 * β) * p ^ (2 * k + 2) - 1) / 2) ∧
      (16 : ℤ) ∣ overpartitionPairEvenDistinct 3 6
        (3 ^ (4 * α + 2) * 5 ^ (2 * β) * p ^ (2 * k + 1) * (24 * m + 13 * p)) ∧
      (16 : ℤ) ∣ overpartitionPairEvenDistinct 3 6
        (3 * 5 ^ (2 * β) * p ^ (2 * k + 1) * (24 * m + 13 * p))

/-- For a prime `p ≥ 5` with `(-1/p) = -1` and all `k, m, α ≥ 0` with `p ∤ m`:
`bped_{3,6}(3^{4α+2}·p^{2k+1}(12m + 5p)) ≡ 0 (mod 16)` (32) and
`bped_{3,6}(3·p^{2k+1}(12m + 5p)) ≡ 0 (mod 16)` (33).
Deviations: the paper allows `p ≥ 3`, but the proof needs `p ∤ 24m + 10p`, which fails for `p = 3`,
and both congruences fail there (`k = α = 0, m = 1`: `bped_{3,6}(729) ≡ 12 (mod 16)`,
`bped_{3,6}(243) ≡ 12 (mod 16)`), so `p ≥ 5` is assumed; the paper's unused quantifier `β` is
dropped.

Source: Adam Paksok and Nipen Saikia, *New Congruences for `[j, k]`-Overpartition Pairs with Even
Parts Distinct*, INTEGERS 26 (2026), Article A118, Theorem 6
(`integers-2026-A118-thm-6`). -/
public theorem_wanted overpartitionPairEvenDistinct_three_six_congr_neg_one_five
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (hleg : legendreSym p (-1) = -1)
    (k m α : ℕ) (hm : ¬ p ∣ m) :
    (16 : ℤ) ∣ overpartitionPairEvenDistinct 3 6
        (3 ^ (4 * α + 2) * p ^ (2 * k + 1) * (12 * m + 5 * p)) ∧
      (16 : ℤ) ∣ overpartitionPairEvenDistinct 3 6 (3 * p ^ (2 * k + 1) * (12 * m + 5 * p))

end

end MetaMathlibExt
