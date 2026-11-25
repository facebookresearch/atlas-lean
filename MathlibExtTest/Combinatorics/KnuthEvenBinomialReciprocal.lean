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
