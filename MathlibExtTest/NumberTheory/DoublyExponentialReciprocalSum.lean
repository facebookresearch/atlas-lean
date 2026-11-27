/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DoublyExponentialReciprocalSum

open MetaMathlibExt

-- At r = 2, the initial nearest-integer choice is a tie and rounds up.
example : pseudoGreedyGap 2 0 = -(1 / 2 : ℝ) := by
  norm_num [pseudoGreedyGap, pseudoGreedyExpansion, pseudoGreedyRemainder, Int.floor_eq_iff]

-- The initial gap for the expansion of one vanishes, so every later gap does too.
example (n : ℕ) : pseudoGreedyGap 1 n = 0 := by
  induction n with
  | zero => exact pseudoGreedyGap_one_zero
  | succ n ih => exact pseudoGreedyGap_succ_eq_zero (by norm_num) ih

-- For r = 3, the first denominator is one and the next remainder is two.
example : pseudoGreedyRemainder 3 1 = 2 := by
  norm_num [pseudoGreedyRemainder, Int.floor_eq_iff]

-- Starting at 3, the recurrence puts the next rounding input exactly at 3/2.
example : (pseudoGreedyExpansion 3 1 : ℝ) + pseudoGreedyGap 3 1 = 3 / 2 := by
  have ha : pseudoGreedyExpansion 3 0 = 1 := by
    norm_num [pseudoGreedyExpansion, pseudoGreedyRemainder, Int.floor_eq_iff]
  have hg : pseudoGreedyGap 3 0 = 1 / 3 := by
    norm_num [pseudoGreedyGap, ha, pseudoGreedyRemainder]
  have h := pseudoGreedyExpansion_succ_eq (r := 3) (by norm_num) 0
  rw [ha, hg] at h
  linarith

example : HasSum (fun n => 1 / (pseudoGreedyExpansion 3 n : ℝ)) 3 :=
  hasSum_one_div_pseudoGreedyExpansion (by norm_num)
