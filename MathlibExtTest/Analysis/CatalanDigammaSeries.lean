/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.CatalanDigammaSeries
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Special values of the Catalan digamma series -/

namespace MetaMathlibExt.CatalanDigammaSeriesTest

example :
    ∑' n : ℕ, (catalan n : ℂ) / (4 ^ n * ∏ j ∈ Finset.Icc 1 n, (1 / 2 + j : ℂ) / j) =
      2 * Complex.log 2 := by
  have h := tsum_catalan_div_four_pow_mul_binom (z := 1 / 2) (by norm_num)
  rw [show (1 / 2 + 1 / 2 : ℂ) = 1 by norm_num, Complex.digamma_one_half, Complex.digamma_one] at h
  rw [h]
  ring

-- The n-weighted specialization at z = 1 gives the value in Remark 1 of Adegoke and Frontczak.
example :
    ∑' n : ℕ, (n : ℂ) * catalan n / (4 ^ n * ∏ j ∈ Finset.Icc 1 n, (1 + j : ℂ) / j) =
      4 * Complex.log 2 - 2 := by
  have h := tsum_nat_mul_catalan_div_four_pow_mul_binom (z := 1) (by norm_num)
  have hhalf : ∀ m : ℕ, (1 / 2 : ℂ) ≠ -(m : ℂ) := by
    intro m hm
    have hre := congrArg Complex.re hm
    norm_num at hre
    linarith [Nat.cast_nonneg (α := ℝ) m]
  rw [h, show (1 + 1 / 2 : ℂ) = 1 / 2 + 1 by ring,
    Complex.digamma_apply_add_one _ hhalf, show (1 - 1 / 2 : ℂ) = 1 / 2 by norm_num,
    Complex.digamma_one, Complex.digamma_one_half]
  ring

end MetaMathlibExt.CatalanDigammaSeriesTest
