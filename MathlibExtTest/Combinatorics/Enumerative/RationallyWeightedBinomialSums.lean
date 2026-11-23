/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.RationallyWeightedBinomialSums
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.Combinatorics.Enumerative.RationallyWeightedBinomialSums` -/

namespace MathlibExtTest.RationallyWeightedBinomialSums

open MetaMathlibExt

-- Edge case `n = 0`: the only term is `binom(0, 0) / 1 = 1`, and `(2 ^ 1 - 1) / 1 = 1`.
example : ∑ k ∈ Finset.range (0 + 1), ((0 : ℕ).choose k : ℚ) / (k + 1) = 1 := by
  rw [sum_choose_div_succ]
  norm_num

-- Row `n = 4`, summed term by term without the theorem:
-- `1/1 + 4/2 + 6/3 + 4/4 + 1/5 = 31/5 = (2 ^ 5 - 1) / 5`.
example : ∑ k ∈ Finset.range (4 + 1), ((4 : ℕ).choose k : ℚ) / (k + 1) = 31 / 5 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose]

-- The same value from the theorem.
example : ∑ k ∈ Finset.range (4 + 1), ((4 : ℕ).choose k : ℚ) / (k + 1) = 31 / 5 := by
  rw [sum_choose_div_succ]
  norm_num

-- Clearing the denominator: `(n + 1) ∑_{k=0}^n binom(n, k) / (k + 1) = 2 ^ (n + 1) - 1`.
example (n : ℕ) :
    ((n : ℚ) + 1) * ∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) / (k + 1) = 2 ^ (n + 1) - 1 := by
  rw [sum_choose_div_succ]
  field_simp

-- The identity in `ℝ`, by casting the rational identity.
example (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) / (k + 1) = (2 ^ (n + 1) - 1) / (n + 1) := by
  have h := congrArg (Rat.cast : ℚ → ℝ) (sum_choose_div_succ n)
  push_cast at h
  exact_mod_cast h

end MathlibExtTest.RationallyWeightedBinomialSums
