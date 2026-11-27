/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.KnuthOldSumBinomialQuotients
import Mathlib.Tactic.NormNum

namespace MathlibExt.Combinatorics.KnuthOldSumWanted

-- At n = 0 the sole term has unit weight and denominator for every j.
example (j : ℕ) :
    ((2 * j + 1).choose 0 : ℚ) * ∑ k ∈ Finset.range 1,
      ((Nat.choose 0 k : ℚ) / (2 * j + 1 + k).choose (2 * j + 1)) *
        knuthOldSumWeight (0 - k) * (-1 : ℚ) ^ k = 1 := by
  simp [knuthOldSumWeight]

-- At n = 2 and j = 1, the terms with k = 1 and k = 2 have denominators 4 and 10.
example :
    (10 : ℚ) * ∑ k ∈ Finset.range 3,
      ((Nat.choose 2 k : ℚ) / (3 + k).choose 3) *
        knuthOldSumWeight (2 - k) * (-1 : ℚ) ^ k = 86 := by
  calc
    _ = ∑ k ∈ Finset.range 3, (Nat.choose 5 (2 - k) : ℚ) *
        knuthOldSumWeight (2 - k) * (-1 : ℚ) ^ k := (knuthOldSum_eq_mul_sum_div 2 1).symm
    _ = 86 := by norm_num [Finset.sum_range_succ, knuthOldSumWeight, Nat.choose]

end MathlibExt.Combinatorics.KnuthOldSumWanted
