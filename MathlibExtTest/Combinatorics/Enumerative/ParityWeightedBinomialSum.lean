/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.ParityWeightedBinomialSum

open Finset MetaMathlibExt

-- At degree zero the odd-index sum is empty.
example :
    ∑ k ∈ range (0 / 2 + 1),
      (Nat.choose 0 (2 * k) : ℚ) * (2 ^ (0 + 1) / 2 ^ (2 * k) - 2 ^ (2 * k + 1)) /
        (2 * k + 1) = 0 := by
  rw [sum_choose_even_two_pow_sub_div]
  decide

-- In degree three the upper endpoint contributes the term with binomial index three.
example :
    ∑ k ∈ range (3 / 2 + 1),
      (Nat.choose 3 (2 * k) : ℚ) * (2 ^ (3 + 1) / 2 ^ (2 * k) - 2 ^ (2 * k + 1)) /
        (2 * k + 1) = 10 := by
  rw [sum_choose_even_two_pow_sub_div]
  norm_num [show Icc 1 ((3 + 1) / 2) = {1, 2} by decide, Nat.choose]

-- In degree four the final even-index term has weight -6.
example :
    ∑ k ∈ Icc 1 ((4 + 1) / 2), (Nat.choose 4 (2 * k - 1) : ℚ) * 2 ^ (2 * k - 1) / k = 24 := by
  rw [← sum_choose_even_two_pow_sub_div]
  norm_num [sum_range_succ, Nat.choose]

-- Degree one has just the first odd-index term and a denominator of one.
example :
    ∑ k ∈ range (1 / 2 + 1), (Nat.choose 1 (2 * k) : ℚ) / (2 * k + 1) = 1 := by
  rw [sum_choose_even_div_eq_sum_choose_odd_div 1 (by decide)]
  norm_num [show Icc 1 ((1 + 1) / 2) = {1} by decide, Nat.choose]

-- In even degree the left sum includes the final even binomial index.
example :
    ∑ k ∈ range (4 / 2 + 1), (Nat.choose 4 (2 * k) : ℚ) / (2 * k + 1) = 16 / 5 := by
  rw [sum_choose_even_div_eq_sum_choose_odd_div 4 (by decide)]
  norm_num [show Icc 1 ((4 + 1) / 2) = {1, 2} by decide, Nat.choose]
