/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.SetTheory.Determinacy.PerfectSet

open Set MathlibExt.SetTheory.Determinacy MathlibExt.SetTheory.DeterminacyWanted

namespace MathlibExtTest.SetTheory.Determinacy.PerfectSet

private def boundaryFamily : Set (Set (ℕ → ℕ)) := {∅, univ}

private theorem boundaryFamily_preimage (f : (ℕ → ℕ) → ℕ → ℕ) (_ : Measurable f) :
    ∀ B ∈ boundaryFamily, f ⁻¹' B ∈ boundaryFamily := by
  intro B hB
  rcases (show B = ∅ ∨ B = univ by simpa [boundaryFamily] using hB) with rfl | rfl <;>
    simp [boundaryFamily]

private theorem boundaryFamily_determined : ∀ B ∈ boundaryFamily, Determined B := by
  intro B hB
  rcases (show B = ∅ ∨ B = univ by simpa [boundaryFamily] using hB) with rfl | rfl
  · exact Or.inr ⟨fun _ => 0, fun _ _ => notMem_empty _⟩
  · exact Or.inl ⟨fun _ => 0, fun _ _ => mem_univ _⟩

-- For the empty payoff, only the countable alternative is possible.
example : (∅ : Set (ℕ → ℕ)).Countable := by
  rcases countable_or_exists_perfect_of_determined (hΓ := boundaryFamily_preimage)
    (hdet := boundaryFamily_determined) (hS := show ∅ ∈ boundaryFamily by simp [boundaryFamily])
    with hc | ⟨_, hsub, hne, _⟩
  · exact hc
  · exact (hne.not_subset_empty hsub).elim

-- For all of Baire space, diagonalization rules out the countable alternative.
example : ∃ P : Set (ℕ → ℕ), P.Nonempty ∧ Perfect P := by
  rcases countable_or_exists_perfect_of_determined boundaryFamily_preimage boundaryFamily_determined
    (show univ ∈ boundaryFamily by simp [boundaryFamily]) with hc | ⟨P, _, hne, hp⟩
  · obtain ⟨f, hf⟩ := countable_iff_exists_surjective.mp (countable_univ_iff.mp hc)
    obtain ⟨n, hn⟩ := hf (fun i => f i i + 1)
    have h : f n n = f n n + 1 := congrFun hn n
    omega
  · exact ⟨P, hne, hp⟩

end MathlibExtTest.SetTheory.Determinacy.PerfectSet
