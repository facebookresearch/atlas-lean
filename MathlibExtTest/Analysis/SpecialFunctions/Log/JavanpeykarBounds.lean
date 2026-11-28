/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecialFunctions.Log.JavanpeykarBounds

open Real Javanpeykar

/-! Concrete instances of the elementary inequalities in Javanpeykar's bounds. -/

/-- Lemma 2.4.3 with `a = 1`, `b = 0` and `x = 3`. -/
example : 3 / 2 + min (0 / 2) (1 - 1 * Real.log (2 * 1)) ≤ 3 - 1 * Real.log (max 1 3) :=
  half_add_min_le_sub_mul_log_max_one (b := 0) one_pos zero_le_one (by norm_num)

/-- The bound by `10 g³` at `g = 2`. -/
example : (4 * ((2 : ℕ) : ℝ) ^ 3 + 5 * ((2 : ℕ) : ℝ) + 1) * Real.log 2 +
    max (((2 : ℕ) : ℝ) / 2 * Real.log (2 * π))
      (((2 : ℕ) : ℝ) / 4 * Real.log (((2 : ℕ) : ℝ) / 2) - ((2 : ℕ) : ℝ) / 4) ≤
    10 * ((2 : ℕ) : ℝ) ^ 3 :=
  numerical_bound_le_ten_mul_cube 2 (by norm_num)

/-- The bounds by a non-Weierstrass point at `g = 2` with `e = Δ = h = 0`, `δ = -160`,
`h_F = (-160 - 8 log(2π)) / 12` and `w = 0`. -/
example : -90 * ((2 : ℕ) : ℝ) ^ 3 - 4 * ((2 : ℕ) : ℝ) * (2 * ((2 : ℕ) : ℝ) - 1) *
    (((2 : ℕ) : ℝ) + 1) * 0 ≤ -160 := by
  have h := constants_of_the_bounds 2 le_rfl 0 (-160) 0 ((-160 - 8 * Real.log (2 * π)) / 12) 0 0
    (by norm_num) ?_ (by push_cast; ring) le_rfl le_rfl ?_
  · exact h.1
  · have := Real.log_pos (by nlinarith [Real.pi_gt_three] : (1 : ℝ) < 2 * π)
    push_cast; nlinarith
  · have := Real.log_pos (by nlinarith [Real.pi_gt_three] : (1 : ℝ) < 2 * π)
    push_cast; nlinarith

/-- `a₃ = 3 / 5`, in lowest terms. -/
example : smallRational 3 = 3 / 5 := by
  rw [smallRational_of_two_le (by norm_num)]; norm_num

example : (smallRational 3).num = 3 := smallRational_num_of_two_le (by norm_num)

example : ((smallRational 3).den : ℤ) = 5 := by
  rw [smallRational_den_of_two_le (by norm_num)]; norm_num

example : 1 / 2 ≤ smallRational 3 ∧ smallRational 3 ≤ 2 / 3 ∧
    Height.logHeight₁ (smallRational 3) ≤ Real.log (2 * ((3 : ℕ) : ℝ)) :=
  smallRational_spec.1 3 (by norm_num)

example : smallRational 2 ≠ smallRational 5 := fun h =>
  absurd (smallRational_spec.2 (by simp) (by simp) h) (by norm_num)

/-- The height-bound inequality at `d = 2`, `g = 2`: `3 log 8 · 4 ≤ 32`. -/
example : 3 * Real.log (2 * ((2 : ℕ) : ℝ) ^ 2) * ((2 : ℕ) : ℝ) ^ 2 ≤
    2 * ((2 : ℕ) : ℝ) ^ 5 / ((2 : ℕ) : ℝ) :=
  three_mul_log_two_mul_sq_mul_sq_le 2 2 le_rfl (by norm_num) le_rfl

/-- The fifth constant of Theorem 1.1.1 at `g = d = 1` with the extreme values of `h` and `w`. -/
example : 1 / 2 * ((1 : ℕ) : ℝ) * (((1 : ℕ) : ℝ) + 1) * 6378033 + 6378028 ≤
    13 * 10 ^ 6 * ((1 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) ^ 5 :=
  (constants_of_theorem_1_1_1 1 1 le_rfl le_rfl 6378033 6378028 (by norm_num)
    (by norm_num)).2.2.2.2
