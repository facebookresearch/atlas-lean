/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Words.ClonedWordPositions

/-! # Regression tests for the positions of letters in cloned words -/

namespace MetaMathlibExt

-- Starting with `b` makes the relative position negative.
private def ba (i : ℕ) : Bool := decide (i % 2 = 1)

private theorem ba_infinite : BothLettersInfinite ba := by
  constructor
  · refine Set.infinite_of_injective_forall_mem (f := fun i : ℕ => 2 * i + 1) ?_ ?_
    · intro i j h
      change 2 * i + 1 = 2 * j + 1 at h
      omega
    · intro i
      change ba (2 * i + 1) = true
      simp only [ba, decide_eq_true_eq]
      omega
  · refine Set.infinite_of_injective_forall_mem (f := fun i : ℕ => 2 * i) ?_ ?_
    · intro i j h
      change 2 * i = 2 * j at h
      omega
    · intro i
      change ba (2 * i) = false
      simp only [ba, decide_eq_false_iff_not]
      omega

private theorem ba_second_true : letterPosition ba true 2 = 3 := by
  have hcount : Nat.count (fun i => ba i = true) 3 = 1 := by decide
  change Nat.nth (fun i => ba i = true) 1 = 3
  rw [← hcount]
  exact Nat.nth_count (by decide)

private theorem ba_second_false : letterPosition ba false 2 = 2 := by
  have hcount : Nat.count (fun i => ba i = false) 2 = 1 := by decide
  change Nat.nth (fun i => ba i = false) 1 = 2
  rw [← hcount]
  exact Nat.nth_count (by decide)

-- First and last copies in the second block of each letter.
example : letterPosition (fun i => ba (i / 3)) true 4 = 9 ∧
    letterPosition (fun i => ba (i / 3)) false 4 = 6 ∧
    relativePosition (fun i => ba (i / 3)) 4 = -3 := by
  simpa [ba_second_true, ba_second_false, relativePosition] using
    letterPosition_clone ba_infinite 3 1 1 (by decide) (by decide)

example : letterPosition (fun i => ba (i / 3)) true 6 = 11 ∧
    letterPosition (fun i => ba (i / 3)) false 6 = 8 ∧
    relativePosition (fun i => ba (i / 3)) 6 = -3 := by
  simpa [ba_second_true, ba_second_false, relativePosition] using
    letterPosition_clone ba_infinite 3 1 3 (by decide) (by decide)

-- A block of size one leaves the positions unchanged, at an arbitrary occurrence.
example (m : ℕ) : relativePosition (fun i => ba (i / 1)) (m + 1) =
    relativePosition ba (m + 1) := by
  have h := (letterPosition_clone ba_infinite 1 m 1 le_rfl le_rfl).2.2
  simpa only [Nat.mul_one, Int.natCast_one, Int.one_mul] using h

end MetaMathlibExt
