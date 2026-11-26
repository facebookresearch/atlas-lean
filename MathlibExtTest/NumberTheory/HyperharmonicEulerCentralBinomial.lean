/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.HyperharmonicEulerCentralBinomial

open MetaMathlibExt

-- At depth zero the finite correction is empty, and the odd harmonic factor is one.
example :
    ((∑' n : ℕ, ((2 * n).choose n : ℝ) / (4 ^ n * ((n : ℝ) + 1) ^ 2) : ℝ) : ℂ) =
      4 * (1 - Real.log 2) := by
  have h := centralBinom_oddMultipleHarmonic_div_succ_sq_tsum 0
  norm_num at h ⊢
  exact h

-- At depth one the correction gives Young's first evaluation in Example 1.
example :
    ((∑' n : ℕ, ((2 * n).choose n : ℝ) * oddMultipleHarmonic 1 n /
        (4 ^ n * ((n : ℝ) + 1) ^ 2) : ℝ) : ℂ) =
      16 - 8 * Real.log 2 - 6 * riemannZeta 2 := by
  have h := centralBinom_oddMultipleHarmonic_div_succ_sq_tsum 1
  norm_num [Finset.Icc_self, mul_sub] at h ⊢
  exact h
