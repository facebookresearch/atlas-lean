/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.Trigonometric.CotBound

/-!
# Tests for cotangent bounds
-/

@[expose] public section

open Complex

example : ‖cos I‖ ≤ 2 * ‖sin I‖ :=
  norm_cos_le_two_mul_norm_sin_of_one_le_abs_im (by simp)

example : sin (3 - 2 * I) ≠ 0 := sin_ne_zero_of_one_le_abs_im (by simp)

/-- On the line `Re z = π / 2`. -/
example (y : ℝ) : ‖cos ((Real.pi / 2 : ℝ) + y * I)‖ ≤ ‖sin ((Real.pi / 2 : ℝ) + y * I)‖ :=
  norm_cos_le_norm_sin_of_cos_re_eq_zero (by simp)

example : sin ((Real.pi / 2 : ℝ) : ℂ) ≠ 0 := sin_ne_zero_of_cos_re_eq_zero (by simp)

/-- Boundary probe: the hypothesis `|Im z| ≥ 1` cannot be dropped, since `sin 0 = 0`. -/
example : ¬ (‖cos (0 : ℂ)‖ ≤ 2 * ‖sin (0 : ℂ)‖) := by simp
