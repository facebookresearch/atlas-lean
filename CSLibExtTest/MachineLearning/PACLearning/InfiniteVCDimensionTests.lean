/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.MachineLearning.PACLearning.Growth

/-!
A kernel-checked counterexample to omitting `HasFiniteVCDim`. The class of all
Boolean functions on `ℕ` shatters every finite set but its canonical natural
supremum is zero. Its two traces on a singleton exceed the resulting bound 1.
Finite enumeration cannot test this unbounded-class behavior.
-/

open Cslib.MachineLearning.PACLearning

namespace CSLibExtTest.MachineLearning.PACLearning

private theorem full_shatters (W : Set ℕ) :
    SetShatters (Set.univ : ConceptClass ℕ Bool) W := by
  classical
  intro V hV
  refine ⟨fun x => decide (x ∈ V), Set.mem_univ _, ?_⟩
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
    decide_eq_true_eq]
  exact ⟨fun h => h.1, fun hx => ⟨hx, hV hx⟩⟩

private theorem full_not_finite :
    ¬ HasFiniteVCDim (Set.univ : ConceptClass ℕ Bool) := by
  intro h
  obtain ⟨N, hN⟩ := hasFiniteVCDim_iff.mp h
  have h := hN (Finset.range (N + 1)) (full_shatters _)
  simp at h

private theorem full_vcDim_zero :
    vcDim (Set.univ : ConceptClass ℕ Bool) = 0 := by
  unfold vcDim
  rw [csSup_of_not_bddAbove full_not_finite]
  simp

private theorem full_traceFamily (s : Finset ℕ) :
    traceFamily Set.univ s = Finset.univ := by
  classical
  ext t
  simp only [mem_traceFamily, Finset.mem_univ, iff_true]
  refine ⟨fun x => decide (x ∈ Subtype.val '' (t : Set s)),
    Set.mem_univ _, fun x => ?_⟩
  simp

-- The omitted-premise version fails on a singleton, not just asymptotically.
private theorem omitted_premise_fails :
    ¬ ((traceFamily (Set.univ : ConceptClass ℕ Bool) {0}).card ≤
    ∑ k ∈ Finset.Iic (vcDim (Set.univ : ConceptClass ℕ Bool)),
      ({0} : Finset ℕ).card.choose k) := by
  rw [full_vcDim_zero, full_traceFamily]
  simp
  decide

end CSLibExtTest.MachineLearning.PACLearning
