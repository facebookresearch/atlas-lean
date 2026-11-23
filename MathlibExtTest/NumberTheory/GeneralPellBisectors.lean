/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GeneralPellBisectors
import Mathlib.Tactic.NormNum.RealSqrt

namespace MetaMathlibExt

/-- `d = 5`, `z = 2`: `x² - 5 y² = ±2` has no integral solution. -/
example (x y : ℤ) : |x ^ 2 - 5 * y ^ 2| ≠ 2 :=
  abs_sq_sub_mul_sq_ne_of_two_mod_four 5 2 rfl rfl x y

#print axioms abs_sq_sub_mul_sq_ne_of_two_mod_four

-- The difference is negative and the first coordinate is negative.
example : Even (-2 : ℤ) ∧ Even (2 : ℤ) :=
  even_of_abs_sq_sub_mul_sq_zero_mod_eight 5 16 rfl rfl (-2) 2 (by decide)

-- A negative coefficient in the same residue class gives a positive difference.
example : Even (2 : ℤ) ∧ Even (-2 : ℤ) :=
  even_of_abs_sq_sub_mul_sq_zero_mod_eight (-3) 16 rfl rfl 2 (-2) (by decide)

-- The boundary value z = 0 requires no positivity hypothesis.
example (x y : ℤ) (h : x ^ 2 = 5 * y ^ 2) : Even x ∧ Even y :=
  even_of_abs_sq_sub_mul_sq_zero_mod_eight 5 0 rfl rfl x y (by rw [h, sub_self, abs_zero])

-- The horizontal line and the line of slope 3/4 have an external bisector of slope -3.
example : ((0 : ℝ) - (-3)) ^ 2 * ((3 / 4) ^ 2 + 1) =
    (3 / 4 - (-3)) ^ 2 * (0 ^ 2 + 1) := by
  apply bisector_slope_equation 0 (3 / 4) (-3) <;> norm_num

end MetaMathlibExt
