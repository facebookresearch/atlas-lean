/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.SetTheory.Determinacy.BaireProperty

open Set Topology MathlibExt.SetTheory.Determinacy MathlibExt.SetTheory.DeterminacyWanted

namespace MathlibExtTest.SetTheory.Determinacy.BaireProperty

private def boundaryFamily : Set (Set (ℕ → ℕ)) := {∅, univ}

private theorem boundaryFamily_preimage (f : (ℕ → ℕ) → ℕ → ℕ) (_ : Measurable f) :
    ∀ B ∈ boundaryFamily, f ⁻¹' B ∈ boundaryFamily := by
  intro B hB
  rcases (show B = ∅ ∨ B = univ by simpa [boundaryFamily] using hB) with rfl | rfl <;>
    simp [boundaryFamily]

private theorem boundaryFamily_determined : ∀ B ∈ boundaryFamily, Determined B := by
  intro B hB
  rcases (show B = ∅ ∨ B = univ by simpa [boundaryFamily] using hB) with rfl | rfl
  · exact determined_of_isOpen isOpen_empty
  · exact determined_of_isOpen isOpen_univ

-- The theorem applies to the trivial family `{∅, ℕ^ℕ}`, with the hypotheses passed by name. The
-- empty payoff goes through the main argument, for a set other than `ℕ^ℕ`.
example : BaireMeasurableSet (∅ : Set (ℕ → ℕ)) :=
  baireMeasurableSet_of_determined (hΓ := boundaryFamily_preimage)
    (hdet := boundaryFamily_determined) (hS := show ∅ ∈ boundaryFamily by simp [boundaryFamily])

-- The whole space is the other member of the trivial family.
example : BaireMeasurableSet (univ : Set (ℕ → ℕ)) :=
  baireMeasurableSet_of_determined boundaryFamily_preimage boundaryFamily_determined
    (show univ ∈ boundaryFamily by simp [boundaryFamily])

-- Every member of a family satisfying the hypotheses differs from an open set by a meagre set.
example {Γ : Set (Set (ℕ → ℕ))}
    (hΓ : ∀ f : (ℕ → ℕ) → ℕ → ℕ, Measurable f → ∀ B ∈ Γ, f ⁻¹' B ∈ Γ)
    (hdet : ∀ B ∈ Γ, Determined B) {S : Set (ℕ → ℕ)} (hS : S ∈ Γ) :
    ∃ u : Set (ℕ → ℕ), IsOpen u ∧ S =ᵇ u :=
  (baireMeasurableSet_of_determined hΓ hdet hS).residualEq_isOpen

-- The family contains the preimage of each member by any Borel map of Baire space, so that
-- preimage also has the property of Baire.
example {Γ : Set (Set (ℕ → ℕ))}
    (hΓ : ∀ f : (ℕ → ℕ) → ℕ → ℕ, Measurable f → ∀ B ∈ Γ, f ⁻¹' B ∈ Γ)
    (hdet : ∀ B ∈ Γ, Determined B) {S : Set (ℕ → ℕ)} (hS : S ∈ Γ)
    {f : (ℕ → ℕ) → ℕ → ℕ} (hf : Measurable f) : BaireMeasurableSet (f ⁻¹' S) :=
  baireMeasurableSet_of_determined hΓ hdet (hΓ f hf S hS)

end MathlibExtTest.SetTheory.Determinacy.BaireProperty
