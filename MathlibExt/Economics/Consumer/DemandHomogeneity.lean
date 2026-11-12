/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Consumer.TwoGood
public import MathlibExt.Economics.SecondWelfareTheorem

@[expose] public section

/-!
# Homogeneity of degree zero of Marshallian demand (Atlas EC02.T03)

Source: J. Levin, *Consumer Theory*, Stanford Econ 202 lecture notes (2004), §2,
Proposition 1 (first part: for all `λ > 0`, `B(λp, λw) = B(p, w)`) and Proposition 3
(Homogeneity: for all `p, w` and `λ > 0`, `x(λp, λw) = x(p, w)`). Levin states these on
`ℝⁿ₊` with `p ∈ ℝⁿ₊`, `w ∈ ℝ₊`; the statements below hold for every consumption set `X` and all
`p`, `w`, so Levin's are the instance `X = SecondWelfareTheorem.consumptionSet L` (used in the
tests).
-/

namespace MathlibExt.Economics.Consumer

open Matrix

open SecondWelfareTheorem (consumptionSet)

/-- Levin, Proposition 1: scaling prices and wealth by the same positive factor leaves the budget
set unchanged. -/
theorem budgetSet_smul {L : Type*} [Fintype L] (X : Set (L → ℝ)) {t : ℝ} (ht : 0 < t)
    (p : L → ℝ) (w : ℝ) : budgetSet X (t • p) (t * w) = budgetSet X p w := by
  ext x
  show (x ∈ X ∧ (t • p) ⬝ᵥ x ≤ t * w) ↔ (x ∈ X ∧ p ⬝ᵥ x ≤ w)
  simp only [smul_dotProduct, smul_eq_mul, mul_le_mul_iff_of_pos_left ht]

/-- Levin, Proposition 3: Marshallian demand is homogeneous of degree zero in prices and wealth. -/
theorem isMarshallianDemand_smul_iff {L : Type*} [Fintype L] (u : (L → ℝ) → ℝ)
    (X : Set (L → ℝ)) {t : ℝ} (ht : 0 < t) (p : L → ℝ) (w : ℝ) (x : L → ℝ) :
    IsMarshallianDemand u X (t • p) (t * w) x ↔ IsMarshallianDemand u X p w x := by
  unfold IsMarshallianDemand
  rw [budgetSet_smul X ht]

/-- Levin, Proposition 1, on Levin's domain: for prices `p ∈ ℝ^L_+`, wealth `w ≥ 0` and `t > 0`,
`B(t p, t w) = B(p, w)` in `ℝ^L_+`. -/
theorem budgetSet_consumptionSet_smul {L : Type*} [Fintype L] {t : ℝ} (ht : 0 < t) {p : L → ℝ}
    (hp : 0 ≤ p) {w : ℝ} (hw : 0 ≤ w) :
    budgetSet (consumptionSet L) (t • p) (t * w) = budgetSet (consumptionSet L) p w := by
  exact budgetSet_smul (consumptionSet L) ht p w

/-- Levin, Proposition 3, on Levin's domain: for prices `p ∈ ℝ^L_+`, wealth `w ≥ 0` and `t > 0`,
`x(t p, t w) = x(p, w)` on `ℝ^L_+`. -/
theorem isMarshallianDemand_consumptionSet_smul_iff {L : Type*} [Fintype L]
    (u : (L → ℝ) → ℝ) {t : ℝ} (ht : 0 < t) {p : L → ℝ} (hp : 0 ≤ p) {w : ℝ} (hw : 0 ≤ w)
    (x : L → ℝ) :
    IsMarshallianDemand u (consumptionSet L) (t • p) (t * w) x ↔
      IsMarshallianDemand u (consumptionSet L) p w x := by
  exact isMarshallianDemand_smul_iff u (consumptionSet L) ht p w x

end MathlibExt.Economics.Consumer
