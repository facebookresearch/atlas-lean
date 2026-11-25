/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ConsecutivePrimePowerSumsLowerBound

namespace MetaMathlibExt.card_consecutivePrimePowerSums_ge.Tests

open Finset

private noncomputable def prefixSum (m : ℕ) : ℕ :=
  ∑ i ∈ range m, Nat.nth Nat.Prime i ^ 2

private noncomputable def blocks (x : ℕ) : Finset (ℕ × ℕ) :=
  (range x ×ˢ Icc 1 x).filter fun lm =>
    ∑ i ∈ range lm.2, Nat.nth Nat.Prime (lm.1 + i) ^ 2 ≤ x

-- A zero cutoff admits no block and has longest length zero.
example : (blocks 0).card = 0 ∧ Nat.findGreatest (fun m => prefixSum m ≤ 0) 0 = 0 := by
  simp [blocks]

-- The prefix of length two first becomes admissible at the inclusive cutoff 13.
example : (0, 2) ∈ blocks 13 ∧ (0, 2) ∉ blocks 12 := by
  norm_num [blocks, sum_range_succ, Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three]

-- At that cutoff the theorem bounds the count below by 2² / 2.
example : 2 ≤ (blocks 13).card := by
  have h2 : prefixSum 2 = 13 := by
    norm_num [prefixSum, sum_range_succ, Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three]
  have h3 : 13 < prefixSum 3 := by
    change 13 < ∑ i ∈ range (2 + 1), Nat.nth Nat.Prime i ^ 2
    rw [sum_range_succ]
    change 13 < prefixSum 2 + Nat.nth Nat.Prime 2 ^ 2
    rw [h2]
    exact Nat.lt_add_of_pos_right (pow_pos (Nat.prime_nth_prime 2).pos _)
  have hmax : Nat.findGreatest (fun m => prefixSum m ≤ 13) 13 = 2 := by
    refine Nat.findGreatest_eq_iff.2 ⟨by decide, fun _ => h2.le, ?_⟩
    intro m hm _
    exact not_le.mpr (h3.trans_le (sum_le_sum_of_subset (range_mono hm)))
  have h := (card_consecutivePrimePowerSums_ge 2 (by decide)).1 13
  change (Nat.findGreatest (fun m => prefixSum m ≤ 13) 13 : ℝ) ^ 2 / 2 ≤ (blocks 13).card at h
  rw [hmax] at h
  norm_num at h
  exact_mod_cast h

end MetaMathlibExt.card_consecutivePrimePowerSums_ge.Tests
