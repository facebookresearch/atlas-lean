/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.CatalanBernstein
import Mathlib.Tactic.NormNum

open Finset

namespace MetaMathlibExt

-- Degree zero retains the constant term even at x = 0.
example :
    ∑ k ∈ range (0 + 1),
        (Nat.choose 0 k : ℂ) / 2 ^ k * (catalan (k + 1) : ℂ) *
          (1 - 0) ^ k * (0 : ℂ) ^ (0 - k) = 1 := by
  rw [sum_choose_catalan_succ_one_sub_pow_mul_pow]
  simp

-- At odd degree three only the constant and quadratic terms survive.
example (x : ℂ) :
    ∑ k ∈ range (3 + 1),
        (Nat.choose 3 k : ℂ) / 2 ^ k * (catalan (k + 1) : ℂ) * (1 - x) ^ k * x ^ (3 - k) =
      1 + 3 / 4 * (1 - x) ^ 2 := by
  rw [sum_choose_catalan_succ_one_sub_pow_mul_pow]
  norm_num [sum_range_succ, Nat.choose]

-- At even degree four the last term uses the first nontrivial Catalan weight, C₂ = 2.
example :
    ∑ k ∈ range (4 + 1),
        (Nat.choose 4 k : ℂ) / 2 ^ k * (catalan (k + 1) : ℂ) *
          (1 - 0) ^ k * (0 : ℂ) ^ (4 - k) = 21 / 8 := by
  rw [sum_choose_catalan_succ_one_sub_pow_mul_pow]
  norm_num [sum_range_succ, Nat.choose, catalan_two]

-- The alternating sum keeps its constant term at degree zero.
example :
    ∑ k ∈ range (0 + 1), (-1 : ℚ) ^ k * (Nat.choose 0 k : ℚ) * (2 * k + 1) / (k + 2) *
        2 ^ (0 + 1) / 2 ^ (2 * k) * catalan k = 1 := by
  rw [sum_neg_one_pow_choose_two_pow_catalan]
  norm_num

-- Degree four includes the nontrivial Catalan weight C₂ on the even-index side.
example :
    ∑ k ∈ range (4 + 1), (-1 : ℚ) ^ k * (Nat.choose 4 k : ℚ) * (2 * k + 1) / (k + 2) *
        2 ^ (4 + 1) / 2 ^ (2 * k) * catalan k = 21 / 8 := by
  rw [sum_neg_one_pow_choose_two_pow_catalan]
  norm_num [sum_range_succ, Nat.choose, catalan_two]

end MetaMathlibExt
