/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.TDA.PersistenceConverseStability

open CategoryTheory Limits MathlibExt.Topology.PersistenceModuleWanted MathlibExt.Topology.TDA
  Metric

/-- Match a closed ray to an open ray and leave a bar of length exactly `2δ` unmatched. -/
example :
    let I (i : Bool) : Set ℝ := if i then Set.Icc 0 2 else Set.Ici 0
    let J (_ : Unit) : Set ℝ := Set.Ioi 0
    let hI : ∀ i, (I i).Nonempty ∧ (I i).OrdConnected := fun i => by
      cases i
      · exact ⟨⟨0, le_rfl⟩, Set.ordConnected_Ici⟩
      · exact ⟨⟨0, le_rfl, zero_le_two⟩, Set.ordConnected_Icc⟩
    let hJ : ∀ j, (J j).Nonempty ∧ (J j).OrdConnected :=
      fun _ => ⟨⟨1, zero_lt_one⟩, Set.ordConnected_Ioi⟩
    Nonempty (Interleaving (∐ fun i => intervalModule ℚ (I i) (hI i).2)
      (∐ fun j => intervalModule ℚ (J j) (hJ j).2) (3 / 2)) := by
  intro I J hI hJ
  apply interleaving_of_isMatching ℚ hI hJ (Iso.refl _) (Iso.refl _) (δ := 1)
  · refine ⟨zero_le_one, fun i _ => i = false, fun _ j j' _ _ => Subsingleton.elim j j',
      fun _ _ _ hi hi' => hi.trans hi'.symm, ?_, ?_, fun _ h => (h false rfl).elim⟩
    · rintro i j (hi : i = false)
      subst i
      change hausdorffEDist (Set.Ici (0 : ℝ)) (Set.Ioi 0) ≤ ENNReal.ofReal 1
      rw [← hausdorffEDist_closure, closure_Ici, closure_Ioi, hausdorffEDist_self]
      exact zero_le
    · intro i hi
      cases i
      · exact (hi () rfl).elim
      · refine ⟨0, ?_⟩
        change Set.Icc (0 : ℝ) 2 ⊆ Set.Icc 0 (0 + 2 * 1)
        norm_num
  · norm_num

/-- The unique empty matching gives an interleaving between two empty coproducts. -/
example :
    let I (i : Empty) : Set ℝ := i.elim
    let hI : ∀ i, (I i).Nonempty ∧ (I i).OrdConnected := fun i => i.elim
    Nonempty (Interleaving (∐ fun i => intervalModule ℚ (I i) (hI i).2)
      (∐ fun i => intervalModule ℚ (I i) (hI i).2) 1) := by
  intro I hI
  apply interleaving_of_isMatching ℚ hI hI (Iso.refl _) (Iso.refl _) (δ := 0)
  · exact ⟨le_rfl, fun _ _ => False, fun i => i.elim, fun i => i.elim,
      fun i => i.elim, fun i => i.elim, fun i => i.elim⟩
  · exact zero_lt_one
