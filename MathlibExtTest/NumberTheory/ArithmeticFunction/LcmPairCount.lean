/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.LcmPairCount

/-!
# Tests for counting pairs with bounded least common multiple
-/

@[expose] public section

open Finset Nat

example : #{q ∈ (12 : ℕ).divisors ×ˢ (12 : ℕ).divisors | Nat.lcm q.1 q.2 = 12} = 15 := by
  decide
example : #(12 ^ 2 : ℕ).divisors = 15 := by decide
example : #{q ∈ (12 : ℕ).divisors ×ˢ (12 : ℕ).divisors | Nat.lcm q.1 q.2 = 12} =
    #(12 ^ 2 : ℕ).divisors :=
  card_filter_lcm_eq_card_divisors_sq (by norm_num)
-- Boundary `n = 1`: only `(1, 1)`.
example : #{q ∈ (1 : ℕ).divisors ×ˢ (1 : ℕ).divisors | Nat.lcm q.1 q.2 = 1} = 1 := by
  rw [card_filter_lcm_eq_card_divisors_sq one_ne_zero]; simp

-- The pair-count bound at its left endpoint `z = 2`: three pairs `(1,1), (1,2), (2,1)`.
example : ((#{q ∈ Icc 1 ⌊(2 : ℝ)⌋₊ ×ˢ Icc 1 ⌊(2 : ℝ)⌋₊ | (Nat.lcm q.1 q.2 : ℝ) ≤ 2} : ℕ) : ℝ) ≤
    20 * 2 * Real.log 2 ^ 3 :=
  card_filter_lcm_le le_rfl
