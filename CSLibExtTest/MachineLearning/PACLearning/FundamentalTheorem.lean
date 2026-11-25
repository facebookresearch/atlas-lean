/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.MachineLearning.PACLearning.FundamentalTheorem

/-!
# Boundary cases for the fundamental theorem of PAC learning

The empty class has no realizable distributions. The singleton indicators on the naturals form
an infinite learnable class, while the class of all binary hypotheses realizes every finite
labelling and hence is unlearnable.
-/

namespace Cslib.MachineLearning.PACLearning.isPACLearnable_realizableFamily_iff_hasFiniteVCDim

example : IsPACLearnable (∅ : ConceptClass ℕ Bool) (realizableFamily ∅) := by
  apply (isPACLearnable_realizableFamily_iff_hasFiniteVCDim _).mpr
  refine hasFiniteVCDim_iff.mpr ⟨0, fun W hW => ?_⟩
  obtain ⟨_, h, _⟩ := hW ∅ (Set.empty_subset _)
  exact h.elim

private def singletons : ConceptClass ℕ Bool := Set.range fun k x : ℕ => decide (x = k)

example : IsPACLearnable singletons (realizableFamily singletons) := by
  apply (isPACLearnable_realizableFamily_iff_hasFiniteVCDim _).mpr
  refine hasFiniteVCDim_iff.mpr ⟨1, fun W hW => ?_⟩
  obtain ⟨_, ⟨k, rfl⟩, hpos⟩ := hW (W : Set ℕ) (Set.Subset.rfl)
  have hsub : W ⊆ {k} := by
    intro x hx
    have h := (Set.ext_iff.mp hpos x).mpr hx
    exact Finset.mem_singleton.mpr (of_decide_eq_true h.1)
  simpa using Finset.card_le_card hsub

example : ¬ IsPACLearnable (Set.univ : ConceptClass ℕ Bool) (realizableFamily Set.univ) := by
  classical
  intro h
  obtain ⟨N, hN⟩ := hasFiniteVCDim_iff.mp
    ((isPACLearnable_realizableFamily_iff_hasFiniteVCDim _).mp h)
  let W := Finset.range (N + 1)
  have hW : SetShatters (Set.univ : ConceptClass ℕ Bool) W := by
    intro V hV
    refine ⟨fun x => decide (x ∈ V), Set.mem_univ _, ?_⟩
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, decide_eq_true_eq]
    exact ⟨And.left, fun hx => ⟨hx, hV hx⟩⟩
  simpa [W] using hN W hW

end Cslib.MachineLearning.PACLearning.isPACLearnable_realizableFamily_iff_hasFiniteVCDim
