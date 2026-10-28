/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthFrameSystemGeneratorsData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthSectionRootAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthMonomialFrames
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemStabilizer
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthXiMatrix

/-! Genuine section/system preservation by the original signs, monomial words, and Xi. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The fifteen original nonzero classes in the actual lattice quotient. -/
def generatedFifthFrameClass (j : Fin 15) : LeechModTwo :=
  leechHyperbolicCoordinates.symm (generatedFifthFrameIncidentClass j)

/-- Every original class has the actual intrinsic root-coordinate embedding. -/
theorem generatedFifthFrameClass_intrinsic (j : Fin 15) :
    generatedAxisE8FrameRootEmbedding (generatedFifthFrameIntrinsicClass j) =
      generatedFifthFrameClass j := by
  change leechHyperbolicCoordinates.symm
    (generatedFifthFrameBinaryMatrix *ᵥ generatedFifthFrameIntrinsicClass j) = _
  rw [generatedFifthFrameIntrinsicClass_certificate]
  rfl

/-- Every nonzero element of the genuine fifth system is an original displayed class. -/
theorem generatedFifthFrameSystem_class_cover (b : LeechModTwo)
    (hb : b ∈ generatedFifthFrameSystem) (hb0 : b ≠ 0) :
    ∃ j : Fin 15, b = generatedFifthFrameClass j := by
  obtain ⟨v, ⟨a, ha⟩, hv⟩ := Submodule.mem_map.mp hb
  have hn : generatedFifthFrameSystemMatrix *ᵥ a ≠ 0 := by
    intro hz
    apply hb0
    rw [← hv, ← ha]
    simp only [Matrix.mulVecLin_apply, hz, map_zero]
  obtain ⟨j, hj⟩ := generatedFifthFrameSystemMatrix_nonzero a hn
  refine ⟨j, ?_⟩
  rw [← hv, ← ha]
  exact congrArg leechHyperbolicCoordinates.symm hj.symm

/-- Permuting the actual fifteen classes preserves the entire actual system subspace. -/
theorem generatedFifthFrameSystem_preserved_of_classes (g : leechIsomSubgroup)
    (hg : ∀ j : Fin 15, ∃ k : Fin 15,
      leechModTwoAction g (generatedFifthFrameClass j) = generatedFifthFrameClass k) :
    generatedFifthFrameSystem.map (leechModTwoAction g).toLinearMap =
      generatedFifthFrameSystem := by
  have hle : generatedFifthFrameSystem.map (leechModTwoAction g).toLinearMap ≤
      generatedFifthFrameSystem := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hb
    by_cases hz : a = 0
    · simp only [hz, map_zero]
      exact Submodule.zero_mem _
    · obtain ⟨j, rfl⟩ := generatedFifthFrameSystem_class_cover a ha hz
      obtain ⟨k, hk⟩ := hg j
      change leechModTwoAction g (generatedFifthFrameClass j) ∈ _
      rw [hk]
      exact generatedFifthMonomial_frame_mem k
  apply SetLike.coe_injective
  have : Finite LeechModTwo := Finite.of_injective
    leechHyperbolicCoordinates leechHyperbolicCoordinates.injective
  apply Set.Finite.eq_of_subset_of_card_le (Set.toFinite _) hle
  exact (Nat.card_congr ((leechModTwoAction g).submoduleMap generatedFifthFrameSystem).toEquiv).le

/-- Each original sign or Xi acts on the actual classes through its certified root matrix. -/
theorem generatedFifthFrameSignXi_action (k : Fin 13) (j : Fin 15) :
    leechModTwoAction (generatedFifthSectionGenerator (generatedFifthFrameSignXiIndex k))
        (generatedFifthFrameClass j) =
      generatedFifthFrameClass (generatedFifthFrameSignXiTarget k j) := by
  rw [← generatedFifthFrameClass_intrinsic j, generatedFifthSectionGenerator_binary,
    generatedFifthFrameSignXi_certificate, generatedFifthFrameClass_intrinsic]

/-- All original twelve signs and Xi preserve the entire original binary fifth system. -/
theorem generatedFifthFrameSignXi_system_preserved (k : Fin 13) :
    generatedFifthFrameSystem.map
        (leechModTwoAction
          (generatedFifthSectionGenerator (generatedFifthFrameSignXiIndex k))).toLinearMap =
      generatedFifthFrameSystem :=
  generatedFifthFrameSystem_preserved_of_classes _
    (fun j => ⟨_, generatedFifthFrameSignXi_action k j⟩)

/-- The full actual simultaneous stabilizer of the selected section and original fifth system. -/
def generatedFifthFrameSystemStabilizer : Subgroup leechIsomSubgroup :=
  generatedAxisE8FrameSystemStabilizer generatedFifthFlagOctad generatedFifthFrameSystem

/-- The original Xi preserves both genuine geometric objects. -/
theorem generatedFifthFrameSystem_xi_mem :
    co1XiIsometry ∈ generatedFifthFrameSystemStabilizer := by
  rw [generatedFifthFrameSystemStabilizer, generatedAxisE8FrameSystemStabilizer_mem]
  refine ⟨(generatedFifth_matrix_stabilizer_iff _).mp generatedFifth_xi_matrix_fixed, ?_⟩
  exact generatedFifthFrameSignXi_system_preserved 12

/-- Each original monomial word preserves both genuine geometric objects. -/
theorem generatedFifthFrameSystem_monomial_mem (k : Fin 6) :
    golayPermutationIsometry (generatedFifthMonomialSpatialPermutation k) ∈
      generatedFifthFrameSystemStabilizer := by
  rw [generatedFifthFrameSystemStabilizer, generatedAxisE8FrameSystemStabilizer_mem]
  refine ⟨?_, generatedFifthMonomial_system_preserved k⟩
  have h := generatedFifthMonomial_section_preserved k
  rw [generatedFifth_monomial_spatial] at h
  simpa only [golayPermutationHom] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
