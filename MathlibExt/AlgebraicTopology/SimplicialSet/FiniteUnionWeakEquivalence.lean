/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
import Mathlib.Order.CompleteLattice.Finset
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakCobaseChange

/-!
# Actual finite subcomplex unions from weak intersections

A nonempty finite family whose every nonempty finite intersection has
weak inclusion into the original simplicial set has weak union inclusion.
The proof uses the native bicartesian subcomplex pushout and actual weak
cobase change along its original monic map. This is the finite-cover
step needed for Rezk's simplex-transition to horn-pullback reduction.
-/

noncomputable section
universe u v
open CategoryTheory Limits

namespace SSet.Subcomplex

variable {X : SSet.{u}}

/-- The whole original binary union is weak in `X` when both pieces and
their SAME original intersection are weak in `X`. -/
theorem realizationWeakEquivalences_union (A B : X.Subcomplex)
    (hA : SSet.realizationWeakEquivalences A.ι) (hB : SSet.realizationWeakEquivalences B.ι)
    (hAB : SSet.realizationWeakEquivalences (A ⊓ B).ι) :
    SSet.realizationWeakEquivalences (A ⊔ B).ι := by
  have hCB : SSet.realizationWeakEquivalences (homOfLE (inf_le_right : A ⊓ B ≤ B)) :=
    SSet.realizationWeakEquivalences.of_postcomp _ _ hB
      (by simpa only [homOfLE_ι] using hAB)
  have square : BicartSq (A ⊓ B) A B (A ⊔ B) := { sup_eq := rfl, inf_eq := rfl }
  have hAU : SSet.realizationWeakEquivalences (homOfLE (le_sup_left : A ≤ A ⊔ B)) :=
    SSet.realizationWeakEquivalences.of_isPushout_mono square.isPushout hCB
  exact SSet.realizationWeakEquivalences.of_precomp _ _ hAU
    (by simpa only [homOfLE_ι] using hA)

private theorem finiteIntersection_inf {I : Type v} (A : I → X.Subcomplex)
    (s : Finset I) (hs : s.Nonempty) (B : X.Subcomplex) :
    (⨅ i ∈ s, A i ⊓ B) = (⨅ i ∈ s, A i) ⊓ B := by
  ext q x
  simp only [Subfunctor.iInf_obj, Subfunctor.min_obj, Set.mem_iInter, Set.mem_inter_iff]
  constructor
  · intro h
    refine ⟨fun i hi => (h i hi).1, ?_⟩
    obtain ⟨i, hi⟩ := hs
    exact (h i hi).2
  · rintro ⟨h, hB⟩ i hi
    exact ⟨h i hi, hB⟩

/-- The SAME complete original finite union is weak whenever every nonempty
finite intersection of its pieces is weak, in arbitrary parameter universes. -/
theorem realizationWeakEquivalences_finiteUnion {I : Type v} (A : I → X.Subcomplex)
    (s : Finset I) (hs : s.Nonempty)
    (h : ∀ t : Finset I, t ⊆ s → t.Nonempty →
      SSet.realizationWeakEquivalences (⨅ i ∈ t, A i).ι) :
    SSet.realizationWeakEquivalences (⨆ i ∈ s, A i).ι := by
  classical
  induction s using Finset.induction_on generalizing A with
  | empty => exact False.elim (Finset.not_nonempty_empty hs)
  | @insert i s hi ih =>
    have hAi : SSet.realizationWeakEquivalences (A i).ι := by
      exact (congrArg (fun K : X.Subcomplex => SSet.realizationWeakEquivalences K.ι)
        (Finset.iInf_singleton i A)).mp (h {i} (by simp) (Finset.singleton_nonempty i))
    by_cases hs' : s.Nonempty
    · have hU : SSet.realizationWeakEquivalences (⨆ j ∈ s, A j).ι :=
        ih A hs' (fun t ht htn => h t (ht.trans (Finset.subset_insert i s)) htn)
      have hI : SSet.realizationWeakEquivalences (⨆ j ∈ s, A j ⊓ A i).ι := by
        apply ih (fun j => A j ⊓ A i) hs'
        intro t ht htn
        have he : (⨅ j ∈ t, A j ⊓ A i) = (⨅ j ∈ insert i t, A j) := by
          rw [Finset.iInf_insert]
          exact (finiteIntersection_inf A t htn (A i)).trans (inf_comm _ _)
        exact (congrArg (fun K : X.Subcomplex => SSet.realizationWeakEquivalences K.ι) he).mpr
          (h (insert i t) (Finset.insert_subset_insert i ht) (by simp))
      have he : (⨆ j ∈ s, A j ⊓ A i) = A i ⊓ (⨆ j ∈ s, A j) := by
        ext q x
        simp only [Subfunctor.iSup_obj, Subfunctor.min_obj, Set.mem_iUnion, Set.mem_inter_iff]
        aesop
      have hIU : SSet.realizationWeakEquivalences (A i ⊓ (⨆ j ∈ s, A j)).ι :=
        (congrArg (fun K : X.Subcomplex => SSet.realizationWeakEquivalences K.ι) he).mp hI
      exact (congrArg (fun K : X.Subcomplex => SSet.realizationWeakEquivalences K.ι)
        (Finset.iSup_insert i s A)).mpr
          (realizationWeakEquivalences_union (A i) (⨆ j ∈ s, A j) hAi hU hIU)
    · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs'
      subst s
      exact (congrArg (fun K : X.Subcomplex => SSet.realizationWeakEquivalences K.ι)
        (Finset.iSup_singleton i A)).mpr hAi

end SSet.Subcomplex
