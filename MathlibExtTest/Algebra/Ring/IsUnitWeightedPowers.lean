/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Ring.IsUnitWeightedPowers
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Order.Field.Rat

/-! Tests for `MathlibExt.Algebra.Ring.IsUnitWeightedPowers`. -/

#check @IsUnit.pow_two_mul_cube_eq_pow_three_mul_sq_iff

/-- The condition `v³ = v'²` for `v = 4`, `v' = 8` survives the unit `u = -1` of `ℤ`. -/
example : ((-1 : ℤ) ^ 2 * 4) ^ 3 = ((-1) ^ 3 * 8) ^ 2 :=
  (isUnit_one.neg.pow_two_mul_cube_eq_pow_three_mul_sq_iff 4 8).mpr (by norm_num)

/-- The condition fails for `v = 1`, `v' = 2`, and stays false after the unit `u = 3` of `ℚ`. -/
example : ((3 : ℚ) ^ 2 * 1) ^ 3 ≠ (3 ^ 3 * 2) ^ 2 := by
  rw [Ne, (IsUnit.mk0 (3 : ℚ) (by norm_num)).pow_two_mul_cube_eq_pow_three_mul_sq_iff 1 2]
  norm_num
