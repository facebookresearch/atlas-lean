/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Sequences.ThrowbackPerfectMixing

/-!
# Tests for perfect mixing of consecutive integers

Check the one-term boundary case and a two-term cycle through its first return.
-/

open MetaMathlibExt

/-- The minimum starting at one returns at time two and distinguishes times zero and one. -/
example :
    let Y : ℕ → ℕ → ℕ := fun k => (throwback id)^[k] (fun i => 1 + i)
    (∀ p, Y 2 p = 1 ↔ Y 0 p = 1) ∧ ¬ ∀ p, Y 0 p = 1 ↔ Y 1 p = 1 := by
  have h := throwback_consecutive_perfect_mixing 1 0 (by decide)
  refine ⟨h.1 0 le_rfl, fun hagree => h.2 0 1 (by decide) (by decide) ?_⟩
  intro i hi p
  simpa [Nat.eq_zero_of_le_zero hi] using hagree p

/-- The first nine position pairs of two and three are distinct, with the first pair
reappearing at time nine even though the other entries have moved. -/
example :
    let Y : ℕ → ℕ → ℕ := fun k => (throwback id)^[k] (fun i => 2 + i)
    let firstFour := fun k => (List.range 4).map (Y k)
    ((List.range 10).map fun k => ((firstFour k).idxOf 2, (firstFour k).idxOf 3)) =
      [(0, 1), (2, 0), (1, 3), (0, 2), (2, 1), (1, 0), (0, 3), (2, 3), (1, 2), (0, 1)] ∧
      firstFour 9 ≠ firstFour 0 := by
  decide
