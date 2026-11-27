/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum
import MathlibExt.Combinatorics.Enumerative.TouchardCatalanIdentity

open Finset MetaMathlibExt

example :
    ∑ k ∈ range (3 + 1), ((3 : ℕ).choose k : ℚ) * (2 * k + 1) / (k + 2) *
      2 / 2 ^ k * catalan k = 19 / 2 := by
  rw [sum_choose_two_mul_add_one_div_catalan]
  decide +kernel

example :
    ∑ k ∈ range (4 + 1), ((4 : ℕ).choose k : ℚ) * (2 * k + 1) / (k + 2) *
      2 / 2 ^ k * catalan k = 177 / 8 := by
  rw [sum_choose_two_mul_add_one_div_catalan]
  decide +kernel

open Finset

namespace MetaMathlibExt

-- At zero, both sums have just the constant term.
example :
    (∑ k ∈ range (0 + 1), (-1 : ℚ) ^ (0 - k) * ((0 : ℕ).choose k : ℚ) *
      (2 * (2 * k + 1)) / (k + 2) * catalan k) = 1 := by
  rw [sum_neg_one_pow_sub_choose_catalan]
  simp [catalan_zero]

-- For even n the last term includes the central choice `n.choose n`.
example :
    (∑ k ∈ range (4 + 1), (-1 : ℚ) ^ (4 - k) * ((4 : ℕ).choose k : ℚ) *
      (2 * (2 * k + 1)) / (k + 2) * catalan k) = 9 := by
  rw [sum_neg_one_pow_sub_choose_catalan]
  norm_num [Finset.sum_range_succ, catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose]

-- For odd n the last even index is n - 1.
example :
    (∑ k ∈ range (5 + 1), (-1 : ℚ) ^ (5 - k) * ((5 : ℕ).choose k : ℚ) *
      (2 * (2 * k + 1)) / (k + 2) * catalan k) = 21 := by
  rw [sum_neg_one_pow_sub_choose_catalan]
  norm_num [Finset.sum_range_succ, catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose]

end MetaMathlibExt
