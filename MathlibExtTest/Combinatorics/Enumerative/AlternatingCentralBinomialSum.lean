/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.AlternatingCentralBinomialSum

open Finset MetaMathlibExt

-- The degree-zero sum consists of the single term with sign (-1)^0.
example :
    ∑ k ∈ range (0 + 1), (-1 : ℤ) ^ (0 - k) * (Nat.choose 0 k : ℤ) * ((2 * k).choose k : ℤ) =
      1 := by
  rw [sum_neg_one_pow_sub_choose_centralBinom]
  decide

-- For odd degree five, the positive sum stops at k = 2 and gives 1 + 20 + 30.
example :
    ∑ k ∈ range (5 + 1), (-1 : ℤ) ^ (5 - k) * (Nat.choose 5 k : ℤ) * ((2 * k).choose k : ℤ) =
      51 := by
  rw [sum_neg_one_pow_sub_choose_centralBinom]
  decide

-- Knuth's old sum takes the central-binomial value at even degree two.
example :
    ∑ k ∈ range (2 + 1), (-1 : ℚ) ^ k * (Nat.choose 2 k : ℚ) * ((2 * k).choose k : ℚ) / 2 ^ k =
      1 / 2 := by
  rw [knuth_old_sum, ite_eq_left (by decide : Even 2),
    show Nat.choose 2 (2 / 2) = 2 from rfl]
  norm_num

-- At odd degree three, the alternating sum vanishes.
example :
    ∑ k ∈ range (3 + 1), (-1 : ℚ) ^ k * (Nat.choose 3 k : ℚ) * ((2 * k).choose k : ℚ) / 2 ^ k =
      0 := by
  rw [knuth_old_sum, ite_eq_right (by decide : ¬ Even 3)]
