/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.AcceleratedZeckendorfGame

/-! # Tests for moves in the Accelerated Zeckendorf Game -/

namespace MetaMathlibExt.accelZeckMove_fib_combine

open Finsupp

-- At the smallest indices, one pair combines and both input piles are exhausted.
example : AccelZeckMove (single 2 1 + single 1 1) (single 3 1) := by
  have h := (accelZeckMove_fib_combine 2 1 (by decide) (by decide)
    (single 2 1 + single 1 1) (by simp) (by simp) (by simp)).1
  change AccelZeckMove _ ((single 2 1 + single 1 1) - single 1 1 - single 2 1 + single 3 1) at h
  simpa using h

-- Two pairs combine at once, leaving one copy at the middle index.
example : AccelZeckMove (single 2 3 + single 1 2) (single 2 1 + single 3 2) := by
  have h := (accelZeckMove_fib_combine 2 3 (by decide) (by decide)
    (single 2 3 + single 1 2) (by simp [Nat.fib_add_two])
    (by simp [Nat.fib_add_two]) (by simp)).1
  change AccelZeckMove _ ((single 2 3 + single 1 2 - single 1 2) - single 2 2 + single 3 2) at h
  simpa [← single_tsub] using h

end MetaMathlibExt.accelZeckMove_fib_combine

namespace MetaMathlibExt.accelZeck_unique_winning_first_move

open Finsupp

-- With six ones, the three legal openings combine one, two, or three pairs.
-- Combining all three pairs is the unique opening that leaves the opponent a losing state.
example {t : ℕ →₀ ℕ} (hm : AccelZeckMove (single 1 6) t) (hl : AccelZeckLosing t) :
    t = single 2 3 := by
  have terminal : AccelZeckLosing (single 1 1 + single 4 1) := by
    apply accelZeckLosing_of_terminal
    rintro u ⟨k, hk, ⟨i, hi, hprev, hcurr, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨i, hi, h, _⟩⟩
    · simp only [Finsupp.add_apply, single_apply] at hprev hcurr
      split_ifs at hprev hcurr <;> omega
    · simp at h
      omega
    · simp at h
      omega
    · simp only [Finsupp.add_apply, single_apply] at h
      split_ifs at h <;> omega
  have reply : AccelZeckWinning (single 1 1 + single 2 1 + single 3 1) := by
    refine .intro _ _ ⟨1, by decide, Or.inl ⟨3, by decide, by simp, by simp, ?_⟩⟩ terminal
    ext i
    simp only [Finsupp.add_apply, tsub_apply, single_apply]
    split_ifs <;> omega
  have threeTwos : AccelZeckLosing (single 2 3) := by
    constructor
    rintro u ⟨k, hk, ⟨i, hi, hprev, hcurr, _⟩ | ⟨h, _⟩ | ⟨h, rfl⟩ | ⟨i, hi, h, _⟩⟩
    · simp only [single_apply] at hprev hcurr
      split_ifs at hprev hcurr <;> omega
    · simp at h
      omega
    · simp at h
      obtain rfl : k = 1 := by omega
      simpa [← single_tsub, add_comm] using reply
    · simp [single_eq_of_ne (show i ≠ 2 by omega)] at h
      omega
  have combineThree : AccelZeckMove (single 1 6) (single 2 3) :=
    ⟨3, by decide, Or.inr (Or.inl ⟨by simp, by simp⟩)⟩
  exact (accelZeck_unique_winning_first_move 6 (.intro _ _ combineThree threeTwos)).unique
    ⟨hm, hl⟩ ⟨combineThree, threeTwos⟩

end MetaMathlibExt.accelZeck_unique_winning_first_move
