/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.AlternatingWeightedCentralBinomialSum
import Mathlib.Tactic.NormNum

open Finset MetaMathlibExt

-- The degree-zero sum includes its single constant term.
example :
    ∑ k ∈ range (0 + 1), (-1 : ℚ) ^ k * (Nat.choose 0 k : ℚ) * 2 ^ (0 : ℕ) / 2 ^ (2 * k) *
        ((2 * k).choose k : ℚ) = 1 := by
  rw [sum_neg_one_pow_choose_two_pow_centralBinom]
  norm_num [Nat.choose]

-- At odd degree three the last term on the left has a negative exponent of two.
example :
    ∑ k ∈ range (3 + 1), (-1 : ℚ) ^ k * (Nat.choose 3 k : ℚ) * 2 ^ (3 : ℕ) / 2 ^ (2 * k) *
        ((2 * k).choose k : ℚ) = 5 / 2 := by
  rw [sum_neg_one_pow_choose_two_pow_centralBinom]
  norm_num [sum_range_succ, Nat.choose]

-- At even degree four the last term on the right includes `choose 4 4`.
example :
    ∑ k ∈ range (4 + 1), (-1 : ℚ) ^ k * (Nat.choose 4 k : ℚ) * 2 ^ (4 : ℕ) / 2 ^ (2 * k) *
        ((2 * k).choose k : ℚ) = 35 / 8 := by
  rw [sum_neg_one_pow_choose_two_pow_centralBinom]
  norm_num [sum_range_succ, Nat.choose]
