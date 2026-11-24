/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ZetaStrideSeries

open MetaMathlibExt

-- At the smallest exponent the zeta sum is empty.
example : ∑' n : ℕ, 1 / (((n : ℝ) + 1) * (2 * ((n : ℝ) + 1) - 1)) = 2 * Real.log 2 := by
  apply Complex.ofReal_injective
  simpa using tsum_inv_pow_mul_two_mul_sub_one 1 (by decide)

-- At the next exponent there is exactly one correction, with coefficient one.
example : ((∑' n : ℕ, 1 / (((n : ℝ) + 1) ^ 2 * (2 * ((n : ℝ) + 1) - 1)) : ℝ) : ℂ) =
    4 * Real.log 2 - riemannZeta 2 := by
  have h := tsum_inv_pow_mul_two_mul_sub_one 2 (by decide)
  norm_num [Finset.Icc_self] at h ⊢
  exact h
