/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Words.PeriodicRelativePosition

/-! # Tests for relative position differences of periodic words -/

namespace MetaMathlibExt

-- The repeating block aaabb has counts three and two, so its lcm is six, not five.
private def block : List Bool := [true, true, true, false, false]
private def word (i : ℕ) : Bool := block.getD (i % block.length) false

private theorem word_infinite : BothLettersInfinite word := by
  constructor
  · refine (Set.infinite_range_of_injective (f := fun n : ℕ => 5 * n) ?_).mono ?_
    · intro a b h
      change 5 * a = 5 * b at h
      omega
    · rintro _ ⟨n, rfl⟩
      have h : (5 * n) % 5 = 0 := by omega
      change block.getD (5 * n % 5) false = true
      rw [h]
      decide
  · refine (Set.infinite_range_of_injective (f := fun n : ℕ => 5 * n + 3) ?_).mono ?_
    · intro a b h
      change 5 * a + 3 = 5 * b + 3 at h
      omega
    · rintro _ ⟨n, rfl⟩
      have h : (5 * n + 3) % 5 = 3 := by omega
      change block.getD ((5 * n + 3) % 5) false = false
      rw [h]
      decide

private noncomputable def diff (n : ℕ) : ℤ :=
  relativePosition word (n + 1) - relativePosition word n

example : ∃ q : ℕ, 0 < q ∧ ∀ n, 1 ≤ n → diff (n + q) = diff n := by
  apply (relativePosition_diff_periodic_of_periodic word_infinite).1
  refine ⟨5, by decide, fun i => ?_⟩
  change block.getD ((i + 5) % 5) false = block.getD (i % 5) false
  rw [Nat.add_mod_right]

example (n : ℕ) (hn : 1 ≤ n) : diff (n + 6) = diff n :=
  (relativePosition_diff_periodic_of_periodic word_infinite).2 block (by decide) (fun _ => rfl) n hn

-- The word's period five is not a period of its relative position differences.
private theorem position_of_count {α : Bool} {n i : ℕ} (hi : word i = α)
    (hc : Nat.count (fun j => word j = α) i = n - 1) : letterPosition word α n = i := by
  rw [letterPosition, ← hc, Nat.nth_count hi]

example : diff (1 + 5) ≠ diff 1 := by
  have h₁a : letterPosition word true 1 = 0 := position_of_count (by decide) (by decide)
  have h₂a : letterPosition word true 2 = 1 := position_of_count (by decide) (by decide)
  have h₆a : letterPosition word true 6 = 7 := position_of_count (by decide) (by decide)
  have h₇a : letterPosition word true 7 = 10 := position_of_count (by decide) (by decide)
  have h₁b : letterPosition word false 1 = 3 := position_of_count (by decide) (by decide)
  have h₂b : letterPosition word false 2 = 4 := position_of_count (by decide) (by decide)
  have h₆b : letterPosition word false 6 = 14 := position_of_count (by decide) (by decide)
  have h₇b : letterPosition word false 7 = 18 := position_of_count (by decide) (by decide)
  change relativePosition word 7 - relativePosition word 6 ≠
    relativePosition word 2 - relativePosition word 1
  simp only [relativePosition, h₁a, h₂a, h₆a, h₇a, h₁b, h₂b, h₆b, h₇b]
  decide

end MetaMathlibExt
