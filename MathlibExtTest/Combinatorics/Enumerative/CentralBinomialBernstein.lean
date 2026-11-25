/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.CentralBinomialBernstein
import Mathlib.Tactic.NormNum

open Finset

namespace MetaMathlibExt

-- At degree zero the Bernstein sum is one even at the endpoint x = 0.
example :
    ∑ k ∈ range (0 + 1),
        (Nat.choose 0 k : ℂ) / 2 ^ k * ((2 * k).choose k : ℂ) *
          (1 - 0) ^ k * (0 : ℂ) ^ (0 - k) = 1 := by
  rw [sum_choose_centralBinom_one_sub_pow_mul_pow]
  simp

-- At odd degree three the expansion stops at the quadratic term.
example (x : ℂ) :
    ∑ k ∈ range (3 + 1),
        (Nat.choose 3 k : ℂ) / 2 ^ k * ((2 * k).choose k : ℂ) * (1 - x) ^ k * x ^ (3 - k) =
      1 + 3 / 2 * (1 - x) ^ 2 := by
  rw [sum_choose_centralBinom_one_sub_pow_mul_pow]
  norm_num [sum_range_succ, Nat.choose]

-- The even-index sum covers both parities of the upper index and the degree-zero boundary.
example :
    ∑ k ∈ range (0 / 2 + 1), (Nat.choose 0 (2 * k) : ℚ) / 2 ^ (2 * k) * ((2 * k).choose k : ℚ) =
      1 := by
  rw [sum_choose_even_centralBinom_div_four_pow]
  norm_num [Nat.choose]

example :
    ∑ k ∈ range (3 / 2 + 1), (Nat.choose 3 (2 * k) : ℚ) / 2 ^ (2 * k) * ((2 * k).choose k : ℚ) =
      5 / 2 := by
  rw [sum_choose_even_centralBinom_div_four_pow]
  norm_num [Nat.choose]

example :
    ∑ k ∈ range (4 / 2 + 1), (Nat.choose 4 (2 * k) : ℚ) / 2 ^ (2 * k) * ((2 * k).choose k : ℚ) =
      35 / 8 := by
  rw [sum_choose_even_centralBinom_div_four_pow]
  norm_num [Nat.choose]

-- Check the degree-zero boundary and a positive odd degree.
example : ∑ k ∈ range (0 + 1), (Nat.choose 0 k : ℚ) / 2 ^ k * ((2 * k).choose k : ℚ) = 1 := by
  rw [sum_choose_centralBinom_div_two_pow]
  norm_num [sum_range_succ, Nat.choose]

example : ∑ k ∈ range (1 + 1), (Nat.choose 1 k : ℚ) / 2 ^ k * ((2 * k).choose k : ℚ) = 2 := by
  rw [sum_choose_centralBinom_div_two_pow]
  norm_num [sum_range_succ, Nat.choose]

-- For n = 2 the last even-index term has signed exponent 2 - 4 = -2.
example : ∑ k ∈ range (2 + 1), (Nat.choose 2 k : ℚ) / 2 ^ k * ((2 * k).choose k : ℚ) = 9 / 2 := by
  rw [sum_choose_centralBinom_div_two_pow]
  norm_num [sum_range_succ, Nat.choose]

-- At n = 3 and x = 2, the alternating signs and both power scalings contribute.
example :
    ∑ k ∈ range (3 + 1),
        (-1) ^ (3 - k) * ((2 * k).choose k : ℂ) / 2 ^ (2 * k) * (Nat.choose 3 k : ℂ) *
          (1 - 2 : ℂ) ^ (3 - k) = 63 / 16 := by
  rw [sum_centralBinom_choose_one_sub_pow_symm]
  norm_num [sum_range_succ, Nat.choose]

end MetaMathlibExt
