/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecialFunctions.Complex.LogMul

set_option autoImplicit false

open Complex
open scoped Real ComplexOrder

-- The source's statement: when `-π < Arg z₁ + Arg z₂ < π` the logarithm is additive.
example {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ slitPlane) (hz₂ : z₂ ∈ slitPlane) (hz₁₂ : z₁ * z₂ ∈ slitPlane)
    (hs : arg z₁ + arg z₂ ∈ Set.Ioo (-π) π) :
    log (z₁ * z₂) = log z₁ + log z₂ := by
  obtain ⟨n, h, -, h0, -⟩ := exists_log_mul_eq_add_log_add_int_mul_two_pi_I hz₁ hz₂ hz₁₂
  rw [h, h0 hs]
  simp

-- The source's "in particular": a positive real first factor needs no correction.
example {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : z ∈ slitPlane) (hrz : (r : ℂ) * z ∈ slitPlane) :
    log (r * z) = log r + log z := by
  obtain ⟨n, h, -, -, h0⟩ :=
    exists_log_mul_eq_add_log_add_int_mul_two_pi_I (ofReal_mem_slitPlane.2 hr) hz hrz
  rw [h, h0 (zero_lt_real.2 hr)]
  simp

-- The correction `n = -1` occurs inside the slit plane: `(-1 + I) ^ 2 = -2 * I`, with
-- `Arg (-1 + I) = 3π/4` and `Arg (-2 * I) = -π/2`.
example : ∃ n : ℤ, n = -1 ∧
    log ((-1 + I) * (-1 + I)) = log (-1 + I) + log (-1 + I) + n * (2 * π * I) := by
  have hz : (-1 + I) ∈ slitPlane := by simp [mem_slitPlane_iff]
  have hprod : (-1 + I) * (-1 + I) = -(2 * I) := by ring_nf; simp [I_sq]; ring
  have hz₂ : (-1 + I) * (-1 + I) ∈ slitPlane := by rw [hprod]; simp [mem_slitPlane_iff]
  obtain ⟨n, h, hn, -, -⟩ := exists_log_mul_eq_add_log_add_int_mul_two_pi_I hz hz hz₂
  refine ⟨n, ?_, h⟩
  have harg : arg ((-1 + I) * (-1 + I)) = arg (-1 + I) + arg (-1 + I) + n * (2 * π) := by
    simpa [log_im] using congr_arg im h
  have hprod_arg : arg ((-1 + I) * (-1 + I)) = -(π / 2) := by
    rw [hprod, show -(2 * I) = ((2 : ℝ) : ℂ) * -I by push_cast; ring,
      arg_real_mul _ (by norm_num : (0 : ℝ) < 2), arg_neg_I]
  have hgt : π / 2 < arg (-1 + I) := by
    have hre : ¬ |arg (-1 + I)| ≤ π / 2 := by rw [abs_arg_le_pi_div_two_iff]; simp
    have hnonneg : 0 ≤ arg (-1 + I) := by rw [arg_nonneg_iff]; simp
    rw [abs_of_nonneg hnonneg] at hre
    exact lt_of_not_ge hre
  have hle := arg_le_pi (-1 + I)
  have hlt : (n : ℝ) < 0 := by nlinarith [Real.pi_pos]
  have hlt' : n < 0 := by exact_mod_cast hlt
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  omega

-- Branch-cut regression: `I` lies in the slit plane but `I * I = -1` does not, so the source's
-- statement does not apply to `z₁ = z₂ = I`. There `arg I + arg I = π`, and the general form
-- gives Mathlib's value `n = 0`, since `log (-1) = π * I` with `arg (-1) = π`.
example : I ∈ slitPlane ∧ I * I ∉ slitPlane ∧ arg I + arg I = π ∧
    log (I * I) = log I + log I := by
  refine ⟨by simp [mem_slitPlane_iff], by simp [mem_slitPlane_iff], by rw [arg_I]; ring, ?_⟩
  obtain ⟨n, h, -, -, -⟩ :=
    exists_log_mul_eq_add_log_add_int_mul_two_pi_I_of_ne_zero (z₁ := I) (z₂ := I) I_ne_zero
      I_ne_zero
  have hn : n = 0 := by
    have harg : arg (I * I) = arg I + arg I + n * (2 * π) := by
      simpa [log_im] using congr_arg im h
    rw [I_mul_I, arg_neg_one, arg_I] at harg
    have : (n : ℝ) * (2 * π) = 0 := by linarith
    exact_mod_cast (mul_eq_zero.1 this).resolve_right (by positivity)
  rw [h, hn]
  simp

-- `z₁ = z₂ = -1` lies off the slit plane, but the general form applies, with the correction
-- `n = -1` (`log 1 = 0 = πi + πi - 2πi`).
example : ∃ n : ℤ, n = -1 ∧ Complex.log ((-1) * (-1)) = Complex.log (-1) + Complex.log (-1) +
    n * (2 * π * I) := by
  obtain ⟨n, h, -⟩ := exists_log_mul_eq_add_log_add_int_mul_two_pi_I_of_ne_zero
    (z₁ := -1) (z₂ := -1) (by norm_num) (by norm_num)
  refine ⟨n, ?_, h⟩
  have harg : arg ((-1) * (-1)) = arg (-1) + arg (-1) + n * (2 * π) := by
    simpa [log_im] using congr_arg im h
  rw [neg_one_mul, neg_neg, arg_one, arg_neg_one] at harg
  have : ((n + 1 : ℤ) : ℝ) * (2 * π) = 0 := by push_cast; linarith
  have h1 : ((n + 1 : ℤ) : ℝ) = 0 := (mul_eq_zero.1 this).resolve_right (by positivity)
  have h2 : n + 1 = 0 := by exact_mod_cast h1
  omega

#print axioms exists_log_mul_eq_add_log_add_int_mul_two_pi_I
#print axioms exists_log_mul_eq_add_log_add_int_mul_two_pi_I_of_ne_zero
