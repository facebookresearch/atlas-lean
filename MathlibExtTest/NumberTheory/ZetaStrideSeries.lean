/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ZetaStrideSeries

open MetaMathlibExt

-- At t = 1 the zeta correction is empty.
example :
    ((∑' n : ℕ, 1 / (((n : ℝ) + 1) * (2 * ((n : ℝ) + 1) - 1)) : ℝ) : ℂ) =
      2 * Real.log 2 := by
  simpa [Finset.Icc_eq_empty_of_lt (by decide : (0 : ℕ) < 1)] using
    tsum_inv_pow_mul_two_mul_sub_one 1 (by decide)

-- At t = 2 the only correction is ζ(2), with coefficient one.
example :
    ((∑' n : ℕ, 1 / (((n : ℝ) + 1) ^ 2 * (2 * ((n : ℝ) + 1) - 1)) : ℝ) : ℂ) =
      4 * Real.log 2 - riemannZeta 2 := by
  rw [tsum_inv_pow_mul_two_mul_sub_one 2 (by decide)]
  norm_num

-- At t = 3 the ζ(2) coefficient doubles and ζ(3) is subtracted once.
example :
    ((∑' n : ℕ, 1 / (((n : ℝ) + 1) ^ 3 * (2 * ((n : ℝ) + 1) - 1)) : ℝ) : ℂ) =
      8 * Real.log 2 - (2 * riemannZeta 2 + riemannZeta 3) := by
  rw [tsum_inv_pow_mul_two_mul_sub_one 3 (by decide),
    show Finset.Icc 1 (3 - 1 : ℕ) = {1, 2} by decide]
  norm_num [Finset.sum_insert]
