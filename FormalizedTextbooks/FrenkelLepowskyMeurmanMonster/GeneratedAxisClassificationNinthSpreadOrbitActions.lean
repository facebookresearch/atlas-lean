/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadOrbitCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadSystemActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsOrbitFamilies
public import Mathlib.Algebra.Group.Action.Pointwise.Finset

/-! Acyclic original-letter transitions give actual sets of nine genuine frame systems.
Their identification with the Ninth-axis short marking is a separate prerequisite. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Pointwise
set_option backward.isDefEq.respectTransparency false

/-- The complete finite set of nine existing source frame-system indices. -/
def generatedNinthSpreadIndexSet (i : Fin 960) : Finset (Fin 270) :=
  Finset.univ.image (generatedNinthSpreadIndices i)

/-- Every recorded index set has exactly nine distinct members. -/
theorem generatedNinth_spread_index_card (i : Fin 960) :
    (generatedNinthSpreadIndexSet i).card = 9 := by
  rw [generatedNinthSpreadIndexSet, Finset.card_image_of_injective _
    (generatedNinth_spread_indices_injective i)]
  simp only [Finset.card_univ, Fintype.card_fin]

/-- Checked incidence sums and retrieval make the complete nine-index sets distinct. -/
theorem generatedNinthSpreadIndexSet_injective :
    Function.Injective generatedNinthSpreadIndexSet := by
  intro i j h
  have hi : (∑ k ∈ generatedNinthSpreadIndexSet i, 2 ^ k.val) =
      ∑ a : Fin 9, 2 ^ (generatedNinthSpreadIndices i a).val := by
    unfold generatedNinthSpreadIndexSet
    rw [Finset.sum_image]
    intro a _ b _ hab
    exact generatedNinth_spread_indices_injective i hab
  have hj : (∑ k ∈ generatedNinthSpreadIndexSet j, 2 ^ k.val) =
      ∑ a : Fin 9, 2 ^ (generatedNinthSpreadIndices j a).val := by
    unfold generatedNinthSpreadIndexSet
    rw [Finset.sum_image]
    intro a _ b _ hab
    exact generatedNinth_spread_indices_injective j hab
  have hh : generatedNinthSpreadHashes i = generatedNinthSpreadHashes j := by
    rw [← generatedNinth_spread_hash_sum i, ← generatedNinth_spread_hash_sum j,
      ← hi, ← hj, h]
  apply Fin.ext
  exact (generatedNinth_spread_lookup i).symm.trans
    ((congrArg generatedNinthSpreadLookup hh).trans (generatedNinth_spread_lookup j))

/-- Every state is an actual set of whole binary lattice-quotient subspaces. -/
def generatedNinthSpreadActual (i : Fin 960) :
    Finset (Submodule (ZMod 2) LeechModTwo) := by
  classical
  exact (generatedNinthSpreadIndexSet i).image generatedAxisE8ActualFrameSystemCandidate

/-- The actual sets contain nine genuine fifteen-frame systems. -/
theorem generatedNinth_spread_actual_card (i : Fin 960) :
    (generatedNinthSpreadActual i).card = 9 := by
  classical
  rw [generatedNinthSpreadActual, Finset.card_image_of_injective _
    generatedAxisE8ActualFrameSystemCandidate_injective, generatedNinth_spread_index_card]

/-- Every member is a genuine system in the selected integral E8 section. -/
theorem generatedNinth_spread_actual_mem (i : Fin 960)
    (W : Submodule (ZMod 2) LeechModTwo) (hW : W ∈ generatedNinthSpreadActual i) :
    W ∈ generatedAxisE8FrameSystems
      (generatedAxisE8CoordinateSection (golayOctadWord generatedFifthFlagOctad)) := by
  classical
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hW
  exact generatedAxisE8ActualFrameSystemCandidate_mem k

/-- These are distinct entire actual subspace sets, not merely distinct chosen labels. -/
theorem generatedNinthSpreadActual_injective : Function.Injective generatedNinthSpreadActual := by
  classical
  intro i j h
  apply generatedNinthSpreadIndexSet_injective
  exact Finset.image_injective generatedAxisE8ActualFrameSystemCandidate_injective h

/-- Every noninitial parent edge acts by its original section isometry on the full set. -/
theorem generatedNinth_spread_edge_actual (i : Fin 960) (hi : i ≠ 0) :
    generatedAxisE8FrameSystemOrbitLetter (generatedNinthSpreadGenerator i) •
      generatedNinthSpreadActual (generatedNinthSpreadParent i) = generatedNinthSpreadActual i := by
  classical
  have hb (j : Fin 9) :
      generatedAxisE8FrameSystemOrbitLetter (generatedNinthSpreadGenerator i) •
        generatedAxisE8ActualFrameSystemCandidate
          (generatedNinthSpreadIndices (generatedNinthSpreadParent i) j) =
      generatedAxisE8ActualFrameSystemCandidate
        (generatedNinthSpreadIndices i (generatedNinthSpreadEdgePermutation i j)) := by
    rw [generatedNinth_spread_system_action, generatedNinth_spread_edge_indices i hi j]
  ext W
  constructor
  · intro hW
    obtain ⟨V, hV, rfl⟩ := Finset.mem_image.mp hW
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hV
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hk
    rw [hb]
    exact Finset.mem_image.mpr ⟨_, Finset.mem_image.mpr
      ⟨generatedNinthSpreadEdgePermutation i j, Finset.mem_univ _, rfl⟩, rfl⟩
  · intro hW
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hW
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨a, ha⟩ := generatedNinth_spread_edge_permutation_surjective i j
    refine Finset.mem_image.mpr
      ⟨generatedAxisE8ActualFrameSystemCandidate
        (generatedNinthSpreadIndices (generatedNinthSpreadParent i) a), ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨_, Finset.mem_image.mpr
        ⟨a, Finset.mem_univ _, rfl⟩, rfl⟩
    · rw [hb, ha]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
