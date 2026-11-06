/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthMonomialFrameData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthFrameIntersectionPreservation

/-! The six original local permutation words preserve the genuine fifth frame system. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The genuine permutation image is the lattice vector from its checked integer coordinates. -/
theorem generatedFifthMonomial_frame_image (k : Fin 6) (j : Fin 15) :
    leechIntegralAction (golayPermutationIsometry (generatedFifthMonomialSpatialPermutation k))
        (generatedFifthFrameNormEightVector j) =
      leechExplicitCoordinates.symm ((generatedFifthMonomialFrameImageInteger k).col j) := by
  apply Subtype.ext
  rw [leechIntegralAction_golayPermutation, generatedFifthFrameNormEightVector_physical,
    ← leechExplicitCoordinates_vector, LinearEquiv.apply_symm_apply]
  funext i
  obtain ⟨a, rfl⟩ := (generatedFifthMonomialSpatialPermutation k).val.surjective i
  simp only [golayIntegerPermute, Equiv.symm_apply_apply]
  rw [generatedFifthMonomialSpatial_forward]
  exact (generatedFifthMonomial_frame_physical_certificate k j a).symm

/-- Each genuine nonzero frame image is its asserted actual quotient class. -/
theorem generatedFifthMonomial_frame_class (k : Fin 6) (j : Fin 15) :
    leechModTwoAction (golayPermutationIsometry (generatedFifthMonomialSpatialPermutation k))
        (leechHyperbolicCoordinates.symm (generatedFifthFrameIncidentClass j)) =
      leechHyperbolicCoordinates.symm
        (generatedFifthFrameIncidentClass (generatedFifthMonomialFrameImageIndex k j)) := by
  have hj : leechHyperbolicCoordinates.symm (generatedFifthFrameIncidentClass j) =
      leechReduction (generatedFifthFrameNormEightVector j) := by
    apply leechHyperbolicCoordinates.injective
    rw [LinearEquiv.apply_symm_apply, generatedFifthFrameNormEightVector_binary]
  rw [hj]
  apply leechHyperbolicCoordinates.injective
  change leechHyperbolicCoordinates (leechReduction
      (leechIntegralAction (golayPermutationIsometry (generatedFifthMonomialSpatialPermutation k))
        (generatedFifthFrameNormEightVector j))) = _
  rw [generatedFifthMonomial_frame_image, leechHyperbolicCoordinates_explicit,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  exact generatedFifthMonomial_frame_binary_certificate k j

/-- Every displayed frame class belongs to the actual sixteen-element system. -/
theorem generatedFifthMonomial_frame_mem (j : Fin 15) :
    leechHyperbolicCoordinates.symm (generatedFifthFrameIncidentClass j) ∈
      generatedFifthFrameSystem := by
  apply (generatedFifthFrameSystem_coordinates _).mpr
  rw [LinearEquiv.apply_symm_apply]
  change ∃ a : Fin 4 → ZMod 2,
    generatedFifthFrameSystemMatrix *ᵥ a = generatedFifthFrameIncidentClass j
  revert j
  decide +kernel

/-- The six genuine permutation words preserve the actual quotient frame system. -/
theorem generatedFifthMonomial_system_preserved (k : Fin 6) :
    generatedFifthFrameSystem.map
        (leechModTwoAction (golayPermutationIsometry
          (generatedFifthMonomialSpatialPermutation k))).toLinearMap =
      generatedFifthFrameSystem := by
  let g := golayPermutationIsometry (generatedFifthMonomialSpatialPermutation k)
  have hle : generatedFifthFrameSystem.map (leechModTwoAction g).toLinearMap ≤
      generatedFifthFrameSystem := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hb
    by_cases hz : a = 0
    · simp only [hz, map_zero]
      exact Submodule.zero_mem _
    · obtain ⟨v, ⟨c, hc⟩, hv⟩ := Submodule.mem_map.mp ha
      have hn : generatedFifthFrameSystemMatrix *ᵥ c ≠ 0 := by
        intro h0
        apply hz
        rw [← hv, ← hc]
        simp only [Matrix.mulVecLin_apply, h0, map_zero]
      obtain ⟨j, hj⟩ := generatedFifthFrameSystemMatrix_nonzero c hn
      have he : a = leechHyperbolicCoordinates.symm (generatedFifthFrameIncidentClass j) := by
        rw [← hv, ← hc]
        exact congrArg leechHyperbolicCoordinates.symm hj.symm
      rw [he]
      change leechModTwoAction (golayPermutationIsometry
        (generatedFifthMonomialSpatialPermutation k))
          (leechHyperbolicCoordinates.symm (generatedFifthFrameIncidentClass j)) ∈ _
      rw [generatedFifthMonomial_frame_class]
      exact generatedFifthMonomial_frame_mem _
  apply SetLike.coe_injective
  have : Finite LeechModTwo := Finite.of_injective
    leechHyperbolicCoordinates leechHyperbolicCoordinates.injective
  apply Set.Finite.eq_of_subset_of_card_le (Set.toFinite _) hle
  exact (Nat.card_congr ((leechModTwoAction g).submoduleMap generatedFifthFrameSystem).toEquiv).le

/-- The genuine permutations preserve the selected physical Golay octad. -/
theorem generatedFifthMonomial_octad_preserved (k : Fin 6) :
    golayPermute (generatedFifthMonomialSpatialPermutation k).val
        (golayOctadWord generatedFifthFlagOctad) =
      golayOctadWord generatedFifthFlagOctad := by
  funext i
  obtain ⟨a, rfl⟩ := (generatedFifthMonomialSpatialPermutation k).val.surjective i
  simp only [golayPermute, Equiv.symm_apply_apply, generatedFifth_flag_word_coordinate]
  rw [generatedFifthMonomialSpatial_forward, generatedFifthMonomial_octad_certificate]

/-- The original local words preserve the actual selected integral E8 section. -/
theorem generatedFifthMonomial_section_preserved (k : Fin 6) :
    generatedAxisE8ImageSection (generatedFifthMonomialSpatialFiber k).val.2
        (golayOctadWord generatedFifthFlagOctad) =
      generatedAxisE8CoordinateSection (golayOctadWord generatedFifthFlagOctad) := by
  rw [generatedFifth_monomial_spatial, generatedAxisE8_permutation_image,
    generatedFifthMonomial_octad_preserved]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
