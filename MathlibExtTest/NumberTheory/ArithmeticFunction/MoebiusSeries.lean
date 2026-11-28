/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.MoebiusSeries
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-!
# Tests for `∑ μ(d) / d^h`
-/

@[expose] public section

open ArithmeticFunction Real
open scoped ArithmeticFunction.Moebius

example : ∑' d : ℕ, (μ d : ℝ) / (d : ℝ) ^ 2 = 6 / π ^ 2 := tsum_moebius_div_sq

-- `h = 4`: `∑ μ(d) / d⁴ = 1 / ζ(4) = 90 / π⁴`.
example : ∑' d : ℕ, (μ d : ℝ) / (d : ℝ) ^ 4 = 90 / π ^ 4 := by
  rw [tsum_moebius_div_pow 4 (by norm_num), show ((4 : ℕ) : ℂ) = 4 by norm_num, riemannZeta_four]
  have : ((π : ℂ) ^ 4 / 90).re = π ^ 4 / 90 := by
    rw [show (π : ℂ) ^ 4 / 90 = ((π ^ 4 / 90 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
  rw [this]
  field_simp

example : 1 ≤ (riemannZeta (3 : ℕ)).re := one_le_re_riemannZeta_natCast 3 (by norm_num)
example : Summable (fun d : ℕ => (μ d : ℝ) / (d : ℝ) ^ 2) := summable_moebius_div_pow 2 le_rfl
example : (riemannZeta (2 : ℕ)).re = ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2 :=
  re_riemannZeta_natCast 2 le_rfl
