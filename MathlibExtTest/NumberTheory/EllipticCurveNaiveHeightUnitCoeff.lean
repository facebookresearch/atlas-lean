/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.EllipticCurveNaiveHeightUnitCoeff

open MetaMathlibExt

-- A nonintegral point with a unit linear coefficient.
example : ¬ Height.mulHeight ![(1 / 4 : ℚ), -41 / 8, 1] < (26 / 5 : ℝ) ^ ((1 : ℝ) / 3) := by
  convert (naiveHeight_lower_bound_of_unit_coeff 1 26 (by decide)).1
    (Or.inl rfl) (by decide) (by decide) (by decide) (1 / 4) (-41 / 8) (by norm_num) using 1
  norm_num

-- A nonintegral point with constant coefficient -1.
example : ¬ Height.mulHeight ![(1 / 4 : ℚ), 7 / 8, 1] < (7 / 5 : ℝ) ^ ((1 : ℝ) / 3) := by
  convert (naiveHeight_lower_bound_of_unit_coeff 7 (-1) (by decide)).2.1
    (by decide) (by decide) (by decide) rfl (1 / 4) (7 / 8) (by norm_num) using 1
  norm_num

-- The point (0, -1) genuinely lies below the bound for coefficients 10 and 1.
example : (0 : ℚ) = 0 ∧ ((-1 : ℚ) = 1 ∨ (-1 : ℚ) = -1) := by
  apply (naiveHeight_lower_bound_of_unit_coeff 10 1 (by decide)).2.2
    (by decide) (by decide) (by decide) rfl 0 (-1) (by norm_num)
  rw [Height.mulHeight_cons_zero, ← Height.mulHeight₁_eq_mulHeight, Height.mulHeight₁_neg,
    Height.mulHeight₁_one]
  calc
    1 = (1 : ℝ) ^ ((1 : ℝ) / 3) := (Real.one_rpow _).symm
    _ < _ := Real.rpow_lt_rpow zero_le_one (by norm_num) (by norm_num)
