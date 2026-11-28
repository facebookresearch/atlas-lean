/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.EssentialSetSequence

/-! # A decreasing sequence in a two-element subset of the multiplicative naturals -/

namespace MetaMathlibExt.exists_decreasing_sequence_of_idempotent_mem.Tests

attribute [local instance] Ultrafilter.semigroup

-- The principal ultrafilter at 1 contains {1, 2}. A shift by 2 rules out 2 in a later term.
example : ∃ C : ℕ → Set ℕ, Antitone C ∧ (∀ n, C n ⊆ {1, 2}) ∧
    ∃ m, ∀ n ≥ m, C n = {1} := by
  let F := {E : Set ℕ | E.Nonempty}
  have hF : IsRamseyFamily F :=
    ⟨⟨{1}, Set.singleton_nonempty 1⟩, Set.not_nonempty_empty,
      fun _ _ h hsub => h.mono hsub, fun _ _ => Set.union_nonempty.mp⟩
  have hsub : ∀ p ∈ betaFamily F, ∀ q ∈ betaFamily F, p * q ∈ betaFamily F := by
    simp [F, betaFamily_nonempty_sets]
  have hp : (pure 1 : Ultrafilter ℕ) ∈ betaFamily F := by simp [F, betaFamily_nonempty_sets]
  have hid : (pure 1 : Ultrafilter ℕ) * pure 1 = pure 1 := by
    apply Ultrafilter.ext
    intro E
    change 1 * 1 ∈ E ↔ 1 ∈ E
    rw [one_mul]
  obtain ⟨C, hanti, hCA, hshift, hCF⟩ :=
    exists_decreasing_sequence_of_idempotent_mem hF hsub (A := {1, 2})
      ⟨pure 1, hp, hid, Ultrafilter.mem_pure.mpr (Set.mem_insert 1 _)⟩
  have hex : ∃ m, 2 ∉ C m := by
    by_cases h : 2 ∈ C 0
    · obtain ⟨m, hm⟩ := hshift 0 2 h
      exact ⟨m, fun h₂ => (by decide : 2 * 2 ∉ ({1, 2} : Set ℕ)) (hCA 0 (hm h₂))⟩
    · exact ⟨0, h⟩
  obtain ⟨m, hm⟩ := hex
  refine ⟨C, hanti, hCA, m, fun n hn => Set.eq_singleton_iff_nonempty_unique_mem.mpr
    ⟨hCF n, ?_⟩⟩
  intro x hx
  rcases hCA n hx with h | h
  · exact h
  · exact (hm (hanti hn (Set.mem_singleton_iff.mp h ▸ hx))).elim

end MetaMathlibExt.exists_decreasing_sequence_of_idempotent_mem.Tests
