/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Sequences.ThrowbackUniformRecurrence

/-!
# Tests for uniform recurrence of throwback sequences

For the increasing sequence of odd numbers, the block of three leaders starting at index
one is `3, 1, 5`. All three recur together with a single gap bound.
-/

namespace MetaMathlibExt.throwbackSequence_uniformly_recurrent

private def odds (n : ℕ) := 2 * n + 1

example : ∃ G, ∀ m, ∃ j, m ≤ j ∧ j ≤ m + G ∧
    throwbackSequence odds j = 3 ∧ throwbackSequence odds (j + 1) = 1 ∧
      throwbackSequence odds (j + 2) = 5 := by
  have hmono : StrictMono odds := by
    intro a b h
    dsimp [odds]
    omega
  obtain ⟨G, hG⟩ := throwbackSequence_uniformly_recurrent odds hmono (by decide) 1 3
  refine ⟨G, fun m => ?_⟩
  obtain ⟨j, hj, hjG, block⟩ := hG m
  exact ⟨j, hj, hjG, (block 0 (by decide)).trans (by decide),
    (block 1 (by decide)).trans (by decide), (block 2 (by decide)).trans (by decide)⟩

end MetaMathlibExt.throwbackSequence_uniformly_recurrent
