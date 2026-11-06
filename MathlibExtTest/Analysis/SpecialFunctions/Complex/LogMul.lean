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
open scoped Real

-- When `-π < Arg z₁ + Arg z₂ < π` the logarithm is additive.
example {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ slitPlane) (hz₂ : z₂ ∈ slitPlane)
    (hs : arg z₁ + arg z₂ ∈ Set.Ioo (-π) π) :
    log (z₁ * z₂) = log z₁ + log z₂ := by
  obtain ⟨n, h, -, h0⟩ := exists_log_mul_eq_add_log_add_int_mul_two_pi_I hz₁ hz₂
  rw [h, h0 hs]
  simp

-- `z₁ = z₂ = -1` lies off the slit plane, but the general form applies, with the correction
-- `n = -1` (`Log 1 = 0 = πi + πi - 2πi`).
example : ∃ n : ℤ, Complex.log ((-1) * (-1)) = Complex.log (-1) + Complex.log (-1) +
    n * (2 * π * I) := by
  obtain ⟨n, h, -⟩ := exists_log_mul_eq_add_log_add_int_mul_two_pi_I_of_ne_zero
    (z₁ := -1) (z₂ := -1) (by norm_num) (by norm_num)
  exact ⟨n, h⟩

#print axioms exists_log_mul_eq_add_log_add_int_mul_two_pi_I
