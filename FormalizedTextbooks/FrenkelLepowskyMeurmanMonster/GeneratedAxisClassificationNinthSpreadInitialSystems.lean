/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadInitialCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsOrbitFamilies

/-! Whole lattice-quotient systems for the specified original nine-index spread. The marking
comparison and its full stabilizer remain separate obligations. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Different specified systems intersect only at the actual zero lattice class. -/
theorem generatedNinth_spread_initial_actual_disjoint (i j : Fin 9) (hij : i ≠ j) :
    Disjoint
      (generatedAxisE8ActualFrameSystemCandidate (generatedNinthSpreadInitialIndex i))
      (generatedAxisE8ActualFrameSystemCandidate (generatedNinthSpreadInitialIndex j)) := by
  apply Submodule.disjoint_def.mpr
  intro v hi hj
  obtain ⟨u, hu, huv⟩ := Submodule.mem_map.mp hi
  obtain ⟨w, hw, hwv⟩ := Submodule.mem_map.mp hj
  obtain ⟨a, rfl⟩ := hu
  obtain ⟨b, rfl⟩ := hw
  have he := generatedAxisE8FrameRootEmbedding_injective (huv.trans hwv.symm)
  rw [generatedAxisE8FrameSystemCandidateMap_bits,
    generatedAxisE8FrameSystemCandidateMap_bits] at he
  have hl := generatedAxisE8FrameLabel_left.injective he
  obtain ⟨ha, _⟩ := generatedNinth_spread_initial_label_intersection i j hij a b hl
  simpa only [ha, map_zero] using huv.symm

/-- The specified initial spread is a set of nine entire actual quotient subspaces. -/
def generatedNinthSpreadInitialActual : Finset (Submodule (ZMod 2) LeechModTwo) := by
  classical
  exact Finset.univ.image (fun i : Fin 9 =>
    generatedAxisE8ActualFrameSystemCandidate (generatedNinthSpreadInitialIndex i))

/-- The whole actual subspaces are distinct, so the initial set has cardinal nine. -/
theorem generatedNinth_spread_initial_actual_card :
    generatedNinthSpreadInitialActual.card = 9 := by
  classical
  have hf : Function.Injective (fun i : Fin 9 =>
      generatedAxisE8ActualFrameSystemCandidate (generatedNinthSpreadInitialIndex i)) := by
    intro i j h
    exact generatedNinth_spread_initial_index_injective
      (generatedAxisE8ActualFrameSystemCandidate_injective h)
  rw [generatedNinthSpreadInitialActual, Finset.card_image_of_injective _ hf]
  simp only [Finset.card_univ, Fintype.card_fin]

/-- Each initial member is a genuine fifteen-frame system in the original selected E8 section. -/
theorem generatedNinth_spread_initial_actual_mem
    (W : Submodule (ZMod 2) LeechModTwo) (hW : W ∈ generatedNinthSpreadInitialActual) :
    W ∈ generatedAxisE8FrameSystems
      (generatedAxisE8CoordinateSection (golayOctadWord generatedFifthFlagOctad)) := by
  classical
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hW
  exact generatedAxisE8ActualFrameSystemCandidate_mem _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
