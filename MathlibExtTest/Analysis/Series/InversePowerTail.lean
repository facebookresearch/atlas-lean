/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Series.InversePowerTail

/-! # Tests for the inverse power tail bound -/

open MetaMathlibExt

-- At the smallest admissible exponent and cutoff, the reciprocal squares start at 2.
example : ∑' k : ℕ, 1 / ((k : ℝ) + 2) ^ 2 < 1 := by
  simpa [Nat.cast_add, add_assoc, one_div] using tsum_inv_pow_succ_lt 2 1 (by decide) (by decide)

-- Starting the reciprocal cubes at 3 gives a bound of 1/8.
example : ∑' k : ℕ, 1 / ((k : ℝ) + 3) ^ 3 < 1 / 8 := by
  convert tsum_inv_pow_succ_lt 3 2 (by decide) (by decide) using 1 <;>
    norm_num [Nat.cast_add, add_assoc, one_div]
