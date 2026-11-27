/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.DeJongLowerBoundArithmetic

/-! Concrete instances of the arithmetic of de Jong's lower bound. -/

#check @DeJong.le_of_half_mul_eq_add_of_le

/-- `g = 2`, `A = 9`, `e = 8`, `w = 6`: `3 · 8 = 6 + 2 · 9`, `6 ≥ 6`, and `8 ≥ 8 · 9 / 9`. -/
example : 8 * (((2 : ℕ) : ℝ) - 1) * 9 / ((2 * ((2 : ℕ) : ℝ) - 1) * (((2 : ℕ) : ℝ) + 1)) ≤ 8 :=
  DeJong.le_of_half_mul_eq_add_of_le 2 (by norm_num) 8 6 9 (by norm_num) (by norm_num)

/-- `g = 1` is allowed: the conclusion reads `e ≥ 0`. -/
example (e w A : ℝ) (heq : 1 / 2 * ((1 : ℕ) : ℝ) * (((1 : ℕ) : ℝ) + 1) * e =
      w + (2 * ((1 : ℕ) : ℝ) - 2) * A) (hw : 1 / 4 * (((1 : ℕ) : ℝ) + 1) * e ≤ w) : 0 ≤ e := by
  have := DeJong.le_of_half_mul_eq_add_of_le 1 le_rfl e w A heq hw
  simpa using this

/-- For `g = 0` the inequality fails: `e = -1`, `w = A = 0` satisfy the hypotheses. -/
example : 1 / 2 * ((0 : ℕ) : ℝ) * (((0 : ℕ) : ℝ) + 1) * (-1) = 0 + (2 * ((0 : ℕ) : ℝ) - 2) * 0 ∧
    1 / 4 * (((0 : ℕ) : ℝ) + 1) * (-1) ≤ 0 ∧
    ¬ 8 * (((0 : ℕ) : ℝ) - 1) * 0 / ((2 * ((0 : ℕ) : ℝ) - 1) * (((0 : ℕ) : ℝ) + 1)) ≤ -1 := by
  norm_num
