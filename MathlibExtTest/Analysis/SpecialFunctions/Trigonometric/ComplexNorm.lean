/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.Trigonometric.ComplexNorm

/-!
# Tests for norms of the complex sine and cosine
-/

@[expose] public section

open Complex

example : normSq (sin I) = Real.sinh 1 ^ 2 := by simp [normSq_sin]

example : normSq (cos I) = 1 + Real.sinh 1 ^ 2 := by simp [normSq_cos]

/-- On the real axis the formula is `sin² x`. -/
example (x : ℝ) : ‖sin (x : ℂ)‖ ^ 2 = Real.sin x ^ 2 := by simp [sq_norm_sin]

example (x : ℝ) : ‖cos (x : ℂ)‖ ^ 2 = Real.cos x ^ 2 := by simp [sq_norm_cos]

/-- Jordan's inequality at the endpoint `d = 1` is an equality. -/
example : |(1 : ℝ)| ≤ |Real.sin (Real.pi * 1 / 2)| :=
  Real.abs_le_abs_sin_pi_mul_div_two (by norm_num)

example : |(-1 / 2 : ℝ)| ≤ |Real.sin (Real.pi * (-1 / 2) / 2)| :=
  Real.abs_le_abs_sin_pi_mul_div_two (by norm_num [abs_div])

/-- `s = 1` is at distance `1` from every even integer, so `‖sin (π/2)‖ ≥ 1`. -/
private lemma one_le_dist_even (k : ℤ) : (1 : ℝ) ≤ ‖(1 : ℂ) - 2 * (k : ℂ)‖ := by
  have h : (1 : ℂ) - 2 * (k : ℂ) = ((1 - 2 * k : ℤ) : ℂ) := by push_cast; ring
  rw [h, Complex.norm_intCast]
  have : (1 - 2 * k : ℤ) ≠ 0 := by omega
  exact_mod_cast Int.one_le_abs this

example : (1 : ℝ) ^ 2 ≤ ‖sin (Real.pi * 1 / 2)‖ ^ 2 :=
  sq_le_sq_norm_sin_pi_mul_div_two zero_le_one 1 one_le_dist_even

/-- `‖cot (π/2)‖ = 0 ≤ 2`. -/
example : sin (Real.pi * 1 / 2) ≠ 0 ∧
    ‖cos (Real.pi * 1 / 2) / sin (Real.pi * 1 / 2)‖ ≤ 1 / 1 + 1 :=
  norm_cos_div_sin_pi_mul_div_two_le one_pos 1 one_le_dist_even

/-- Boundary probe: `ρ = 0` is always admissible and gives the trivial bound. -/
example (s : ℂ) : (0 : ℝ) ^ 2 ≤ ‖sin (Real.pi * s / 2)‖ ^ 2 :=
  sq_le_sq_norm_sin_pi_mul_div_two le_rfl s fun _ => norm_nonneg _
