/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# The Fisher price index and time reversal

Over a finite basket: Laspeyres is the cost of the base basket at current prices over
its cost at base prices; Paasche is the cost of the current basket at current prices
over its cost at base prices; Fisher is the geometric mean of the two. Time reversal
says that swapping the two periods (prices and baskets both swapped) gives the
reciprocal index: the forward and reversed Fisher indices multiply to `1`. Only the
four basket-value sums are assumed strictly positive; positivity of individual
prices or quantities is not assumed. Factor reversal, circularity, and any
cost-of-living interpretation are not claimed.

## Main results

* `fisher_time_reversal`: forward times reversed Fisher index equals `1` under strictly
  positive basket values.
* `fisher_time_reversal_example`: two-good basket, base prices `(1, 2)`, current
  `(2, 3)`, basket `(1, 1)` both periods.

## References

* Australian Bureau of Statistics, price index theory (Laspeyres/Paasche/Fisher
  definitions and weighting conventions).
* MIT 14.05 Intermediate Macroeconomics, Fall 2024, syllabus (measurement scope).
-/

@[expose] public section

namespace MathlibExt.Economics.Macro.FisherIndex

/-- **Laspeyres price index** over the finite basket `s`: the cost of the base-period
basket `q0` at current prices `p1`, over its cost at base prices `p0`. -/
noncomputable def laspeyres {ι : Type*} (p0 p1 q0 : ι → ℝ) (s : Finset ι) : ℝ :=
  (∑ i ∈ s, p1 i * q0 i) / (∑ i ∈ s, p0 i * q0 i)

/-- **Paasche price index** over the finite basket `s`: the cost of the current-period
basket `q1` at current prices `p1`, over its cost at base prices `p0`. -/
noncomputable def paasche {ι : Type*} (p0 p1 q1 : ι → ℝ) (s : Finset ι) : ℝ :=
  (∑ i ∈ s, p1 i * q1 i) / (∑ i ∈ s, p0 i * q1 i)

/-- **Fisher price index**: the geometric mean of the Laspeyres and Paasche indices. -/
noncomputable def fisherIndex {ι : Type*} (p0 p1 q0 q1 : ι → ℝ) (s : Finset ι) : ℝ :=
  Real.sqrt (laspeyres p0 p1 q0 s * paasche p0 p1 q1 s)

/-- **Fisher time reversal.** Swapping the two periods (base/current, with baskets
swapped accordingly) gives the reciprocal index: the forward and reversed Fisher indices
multiply to `1`. The hypothesis is that all four basket values are strictly positive, so
every ratio is well defined and every square root is of a positive number. This follows
from ratio cancellation (`div_mul_div_cancel₀'`) and square-root product identities
(`Real.sqrt_mul`). -/
theorem fisher_time_reversal {ι : Type*} {p0 p1 q0 q1 : ι → ℝ} {s : Finset ι}
    (h00 : 0 < ∑ i ∈ s, p0 i * q0 i) (h10 : 0 < ∑ i ∈ s, p1 i * q0 i)
    (h01 : 0 < ∑ i ∈ s, p0 i * q1 i) (h11 : 0 < ∑ i ∈ s, p1 i * q1 i) :
    fisherIndex p1 p0 q1 q0 s * fisherIndex p0 p1 q0 q1 s = 1 := by
  have h00' : (∑ i ∈ s, p0 i * q0 i) ≠ 0 := ne_of_gt h00
  have h10' : (∑ i ∈ s, p1 i * q0 i) ≠ 0 := ne_of_gt h10
  have h01' : (∑ i ∈ s, p0 i * q1 i) ≠ 0 := ne_of_gt h01
  have h11' : (∑ i ∈ s, p1 i * q1 i) ≠ 0 := ne_of_gt h11
  have hA : 0 ≤ laspeyres p1 p0 q1 s * paasche p1 p0 q0 s := by
    unfold laspeyres paasche
    positivity
  have hprod : (laspeyres p1 p0 q1 s * paasche p1 p0 q0 s) *
      (laspeyres p0 p1 q0 s * paasche p0 p1 q1 s) = 1 := by
    unfold laspeyres paasche
    field_simp [h00', h10', h01', h11']
  unfold fisherIndex
  rw [← Real.sqrt_mul hA, hprod, Real.sqrt_one]

/-- Concrete two-good basket: base prices `(1, 2)`, current prices `(2, 3)`, basket
`(1, 1)` in both periods. Then Laspeyres = Paasche = `5 / 3`, so the forward Fisher index
is `5 / 3` and the reversed index is `3 / 5`. Prove by applying `fisher_time_reversal`,
discharging the four positivity hypotheses with `simp [Fin.sum_univ_two]` and `norm_num`. -/
theorem fisher_time_reversal_example :
    fisherIndex ![2, 3] ![1, 2] ![1, 1] ![1, 1] (Finset.univ : Finset (Fin 2)) *
        fisherIndex ![1, 2] ![2, 3] ![1, 1] ![1, 1] (Finset.univ : Finset (Fin 2)) = 1 := by
  apply fisher_time_reversal <;> simp [Fin.sum_univ_two] <;> norm_num

end MathlibExt.Economics.Macro.FisherIndex
