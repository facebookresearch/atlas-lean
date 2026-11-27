/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GleefulNumbers
import Mathlib.Tactic.NormNum

/-! # Endpoint tests for the maximal gleeful chain length -/

namespace MathlibExtTest.GleefulNumbers

open MetaMathlibExt Real

private lemma first_six_squares :
    ∑ i ∈ Finset.range 6, Nat.nth Nat.Prime i ^ 2 = 377 := by
  have hp : Nat.nth Nat.Prime 5 = 13 := Nat.nth_count (by decide : Nat.Prime 13)
  norm_num [Finset.sum_range_succ, hp]

private lemma first_seven_squares :
    ∑ i ∈ Finset.range 7, Nat.nth Nat.Prime i ^ 2 = 666 := by
  have hp : Nat.nth Nat.Prime 6 = 17 := Nat.nth_count (by decide : Nat.Prime 17)
  rw [Finset.sum_range_succ, first_six_squares, hp]
  decide

-- Just below the next sum, the maximal length still equals the minimum cutoff.
example : log 6 < log 665 / 3 * (1 / (log 3 / log 6)) := by
  have h := log_maxChainLength_bounds 2 6 6 665 (by decide) (by decide) (by decide)
    (by rw [first_six_squares]; decide) (by rw [first_seven_squares]; decide)
  norm_num at h ⊢
  exact h.1

-- At the next sum, the length increases to seven while the constants still use six.
example : log 666 / 3 * (1 / (log 7 / log 6 + log (log 49) / log 6 * (2 / 3))) ≤ log 7 := by
  have h := log_maxChainLength_bounds 2 6 7 666 (by decide) (by decide) (by decide)
    first_seven_squares.le (by
      rw [Finset.sum_range_succ, first_seven_squares]
      exact Nat.lt_add_of_pos_right (pow_pos (Nat.prime_nth_prime 7).pos 2))
  norm_num at h ⊢
  exact h.2

end MathlibExtTest.GleefulNumbers
