/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.Combinatorics.KnuthOldSumPowers

namespace MathlibExt.Combinatorics.KnuthOldSumWanted

-- At n = 0 the only term has weight 1 for every j.
example (j : ℕ) :
    (∑ k ∈ Finset.range (0 + 1), ((0 + 2 * j + 1).choose (0 - k) : ℚ) *
      knuthOldSumWeight (0 - k) * (-1 : ℚ) ^ k) = 1 := by
  rw [knuthOldSum_eq_sum_pow]
  norm_num

-- With n = 2 and j = 1 the alternating terms are 100, -15 and 1.
example :
    (∑ k ∈ Finset.range 3, ((2 + k).choose k : ℚ) *
      (((2 : ℚ) ^ k + (4 : ℚ) ^ k * (3 : ℚ) ^ (2 - k)) / 2)) = 86 := by
  rw [← knuthOldSum_eq_sum_pow 2 1]
  norm_num [Finset.sum_range_succ, knuthOldSumWeight, Nat.choose]

end MathlibExt.Combinatorics.KnuthOldSumWanted
