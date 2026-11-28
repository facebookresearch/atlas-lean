/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.PoleOrderAtInfinity

/-!
# Tests for the pole orders at infinity of functions on a Weierstrass cubic

Examples on the curve `y² + y = x³ - x` over `ℚ`.
-/

@[expose] public section

namespace WeierstrassCurve.PoleOrderAtInfinityTest

open Polynomial

/-- The curve `y² + y = x³ - x` over `ℚ`. -/
noncomputable abbrev E : WeierstrassCurve ℚ := { a₁ := 0, a₂ := 0, a₃ := 1, a₄ := -1, a₆ := 0 }

/-- `x² + 5 x y` has a pole of order `max (4, 5) = 5` at infinity. -/
example : E.valuationAtInfinity (algebraMap _ E.toAffine.FunctionField
    (AdjoinRoot.of E.toAffine.polynomial (X ^ 2) +
      AdjoinRoot.of E.toAffine.polynomial (C 5 * X) * E.affineY)) = WithZero.exp 5 := by
  rw [valuationAtInfinity_add_mul_affineY]
  have h2 : (X ^ 2 : ℚ[X]).natDegree = 2 := natDegree_X_pow 2
  have h1 : (C 5 * X : ℚ[X]).natDegree = 1 := natDegree_C_mul_X 5 (by norm_num)
  have h2' : (X ^ 2 : ℚ[X]) ≠ 0 := pow_ne_zero 2 X_ne_zero
  have h1' : (C 5 * X : ℚ[X]) ≠ 0 := by simp
  simp only [h2, h1, h2', h1', ↓reduceIte]
  rw [max_eq_right (by rw [WithZero.exp_le_exp]; norm_num)]
  norm_num

/-- `2 - x` has a pole of order exactly `2` at infinity. -/
example : E.valuationAtInfinity (algebraMap _ E.toAffine.FunctionField
    (algebraMap ℚ _ 2 + algebraMap ℚ _ (-1) * E.affineX)) = WithZero.exp 2 :=
  (E.valuationAtInfinity_add_mul_affineX_eq_exp_two_iff 2 (-1)).mpr (by norm_num)

/-- `1 + x + 3 y` has a pole of order exactly `3` at infinity. -/
example : E.valuationAtInfinity (algebraMap _ E.toAffine.FunctionField
    (algebraMap ℚ _ 1 + algebraMap ℚ _ 1 * E.affineX + algebraMap ℚ _ 3 * E.affineY)) =
      WithZero.exp 3 :=
  (E.valuationAtInfinity_add_mul_affineX_add_mul_affineY_eq_exp_three_iff 1 1 3).mpr
    (by norm_num)

/-- `y` lies in `L(3[O])` but not in `L(2[O])`. -/
example : E.valuationAtInfinity (algebraMap _ E.toAffine.FunctionField E.affineY) ≤
    WithZero.exp 3 :=
  (E.valuationAtInfinity_le_exp_three_iff _).mpr ⟨0, 0, 1, by simp⟩

/-- `y` does not lie in `L(2[O])`. -/
example : ¬ E.valuationAtInfinity (algebraMap _ E.toAffine.FunctionField E.affineY) ≤
    WithZero.exp 2 := by
  rw [valuationAtInfinity_affineY, WithZero.exp_le_exp]
  norm_num

#check @WeierstrassCurve.valuation_map_polynomial
#check @WeierstrassCurve.of_C_eq_algebraMap
#check @WeierstrassCurve.existsUnique_eq_add_mul_affineY
#check @WeierstrassCurve.valuationAtInfinity_polynomial
#check @WeierstrassCurve.valuationAtInfinity_polynomial_mul_affineY
#check @WeierstrassCurve.valuationAtInfinity_add_mul_affineY
#check @WeierstrassCurve.valuationAtInfinity_add_mul_affineY_le_exp_iff
#check @WeierstrassCurve.valuationAtInfinity_le_exp_two_iff
#check @WeierstrassCurve.valuationAtInfinity_le_exp_three_iff
#check @WeierstrassCurve.valuationAtInfinity_add_mul_affineX_eq_exp_two_iff
#check @WeierstrassCurve.valuationAtInfinity_add_mul_affineX_add_mul_affineY_eq_exp_three_iff

end WeierstrassCurve.PoleOrderAtInfinityTest
