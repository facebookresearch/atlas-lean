/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum
import MathlibExt.Combinatorics.KnuthEvenBinomialReciprocal

example : (∑ k ∈ Finset.range (0 / 2 + 1), ((0 : ℕ).choose (2 * k) : ℚ) / (2 * k + 1)) = 1 := by
  rw [MetaMathlibExt.sum_choose_even_div_two_mul_add_one]
  norm_num

example : (∑ k ∈ Finset.range (5 / 2 + 1), ((5 : ℕ).choose (2 * k) : ℚ) / (2 * k + 1)) = 16 / 3 := by
  rw [MetaMathlibExt.sum_choose_even_div_two_mul_add_one]
  norm_num

open Finset

example : (∑ k ∈ range (0 + 1),
    (-1 : ℚ) ^ (0 - k) * ((0 : ℕ).choose k : ℚ) * 2 ^ (2 * k) / (k + 1)) = 1 := by
  rw [MetaMathlibExt.sum_neg_one_pow_sub_choose_four_pow_div_succ (n := 0)]
  norm_num [sum_range_succ]

example : (∑ k ∈ range (1 + 1),
    (-1 : ℚ) ^ (1 - k) * ((1 : ℕ).choose k : ℚ) * 2 ^ (2 * k) / (k + 1)) = 1 := by
  rw [MetaMathlibExt.sum_neg_one_pow_sub_choose_four_pow_div_succ (n := 1)]
  norm_num [sum_range_succ]

example : (∑ k ∈ range (2 + 1),
    (-1 : ℚ) ^ (2 - k) * ((2 : ℕ).choose k : ℚ) * 2 ^ (2 * k) / (k + 1)) = 7 / 3 := by
  rw [MetaMathlibExt.sum_neg_one_pow_sub_choose_four_pow_div_succ (n := 2)]
  norm_num [sum_range_succ]
