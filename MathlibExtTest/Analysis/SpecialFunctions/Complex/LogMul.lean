/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecialFunctions.Complex.LogMul

set_option autoImplicit false

open Complex Real

-- When `|Arg z₁ + Arg z₂| < π` the logarithm is additive.
example {z₁ z₂ : ℂ} (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0) (hs : |arg z₁ + arg z₂| < π) :
    log (z₁ * z₂) = log z₁ + log z₂ := by
  obtain ⟨n, -, h, h0⟩ := log_mul_eq_add_log_add_int hz₁ hz₂
  rw [h, h0 hs]
  simp

-- `z₁ = z₂ = -1`, where the correction is `n = -1` (`Log 1 = 0 = πi + πi - 2πi`).
example : ∃ n : ℤ, n ∈ ({-1, 0, 1} : Set ℤ) ∧
    Complex.log ((-1) * (-1)) = Complex.log (-1) + Complex.log (-1) + n * (2 * π * I) := by
  obtain ⟨n, hn, h, -⟩ := log_mul_eq_add_log_add_int (z₁ := -1) (z₂ := -1) (by norm_num)
    (by norm_num)
  exact ⟨n, hn, h⟩

#print axioms log_mul_eq_add_log_add_int
