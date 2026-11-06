/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhFrameOrbitPlane
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhFrameOrbitBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhMonomialFrameLower

/-! The actual seventh spatial group has 27 frame images and frame stabilizer order 5898240. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The genuine selected-to-seventh coordinate transport as a Leech isometry. -/
def generatedSeventhFrameTransport : leechIsomSubgroup :=
  golayPermutationIsometry generatedSeventhTriangleTransportPermutation

/-- The actual coordinate transport preserves the triangle and sends the entire selected section. -/
theorem generatedSeventhFrameTransport_flag :
    (generatedAxisE8CoordinateSection (golayOctadWord generatedSeventhSectionOctad),
      leechSeventhE8A2Plane 537) = generatedSeventhFrameTransport •
        (generatedAxisE8CoordinateSection (golayOctadWord generatedFifthFlagOctad),
          leechSeventhE8A2Plane 537) := by
  apply Prod.ext
  · exact (leechSeventh_coordinate_section_permutation _ _
      generatedSeventhTriangleTransportPermutation
      generatedSeventh_triangle_transport_spec.2.2.2).symm
  · exact ((leechSeventhTriangle_projection_fixed_iff _).mp
      (generatedSeventh_permutation_plane_fixed _ generatedSeventh_triangle_transport_fixed)).symm

/-- The original signed section word is a genuine selected triangle-flag fixer. -/
def generatedSeventhFrameSelectedElement (k : Fin 27) :
    MulAction.stabilizer leechIsomSubgroup
      (generatedAxisE8CoordinateSection (golayOctadWord generatedFifthFlagOctad),
        leechSeventhE8A2Plane 537) := by
  refine ⟨leechSeventhFrameWord (leechSeventhFrameOrbitWord k), ?_⟩
  change _ • (generatedAxisE8CoordinateSection (golayOctadWord generatedFifthFlagOctad),
    leechSeventhE8A2Plane 537) = _
  apply Prod.ext
  · exact (generatedAxisE8SectionStabilizer_mem _ _).mp (leechSeventhFrameWord_mem _)
  · exact leechSeventhFrameOrbitWord_plane_fixed k

/-- Each finite witness is conjugated into the actual seventh matrix group. -/
def generatedSeventhFrameOrbitElement (k : Fin 27) : generatedSeventhSpatialStabilizer := by
  let e := MulAction.stabilizerEquivStabilizer generatedSeventhFrameTransport_flag
    (generatedSeventhFrameSelectedElement k)
  refine ⟨e.val, ?_⟩
  rw [generatedSeventhSpatialStabilizer_eq_flag]
  exact e.property

/-- The transported witness is precisely the genuine original signed word conjugate. -/
theorem generatedSeventhFrameOrbitElement_val (k : Fin 27) :
    (generatedSeventhFrameOrbitElement k).val = generatedSeventhFrameTransport *
      leechSeventhFrameWord (leechSeventhFrameOrbitWord k) * generatedSeventhFrameTransport⁻¹ := by
  exact MulAction.stabilizerEquivStabilizer_apply generatedSeventhFrameTransport_flag
    (generatedSeventhFrameSelectedElement k)

/-- The genuine quotient-coordinate target of each actual seventh spatial word. -/
def generatedSeventhFrameOrbitTarget (k : Fin 27) : LeechModTwo :=
  leechModTwoAction generatedSeventhFrameTransport
    (generatedAxisE8FrameRootEmbedding
      (generatedAxisE8FrameLabelBits (leechSeventhFrameOrbitLabel k)))

/-- All 27 targets are distinct actual Leech quotient classes. -/
theorem generatedSeventhFrameOrbitTarget_injective :
    Function.Injective generatedSeventhFrameOrbitTarget := by
  intro i j h
  apply leechSeventhFrameOrbitLabel_injective
  apply generatedAxisE8FrameLabelEquiv.injective
  apply generatedAxisE8FrameRootEmbedding_injective
  exact (leechModTwoAction generatedSeventhFrameTransport).injective h

/-- The complete original signed word sends the actual base frame to the certified target. -/
theorem generatedSeventhFrameOrbitElement_action (k : Fin 27) :
    leechModTwoAction (generatedSeventhFrameOrbitElement k).val
      (leechReduction (leechCoordinateFrameLattice 0)) = generatedSeventhFrameOrbitTarget k := by
  have ht : leechModTwoAction generatedSeventhFrameTransport⁻¹
      (leechReduction (leechCoordinateFrameLattice 0)) =
        leechReduction (leechCoordinateFrameLattice 0) :=
    leechSeventhFrame_permutation_fixed generatedSeventhTriangleTransportPermutation⁻¹
  rw [generatedSeventhFrameOrbitElement_val, map_mul, map_mul]
  change leechModTwoAction generatedSeventhFrameTransport
    (leechModTwoAction (leechSeventhFrameWord (leechSeventhFrameOrbitWord k))
      (leechModTwoAction generatedSeventhFrameTransport⁻¹
        (leechReduction (leechCoordinateFrameLattice 0)))) = _
  rw [ht, ← leechSeventhFrame_base_embedding, leechSeventhFrameWord_binary,
    leechSeventhFrameOrbitWord_binary]
  rfl

/-- The 27 genuinely reached classes embed in the full actual seventh spatial frame orbit. -/
def generatedSeventhFrameOrbitWitness (k : Fin 27) :
    MulAction.orbit generatedSeventhSpatialStabilizer
      (leechReduction (leechCoordinateFrameLattice 0)) :=
  ⟨generatedSeventhFrameOrbitTarget k,
    ⟨generatedSeventhFrameOrbitElement k, generatedSeventhFrameOrbitElement_action k⟩⟩

/-- The full genuine seventh spatial group has exactly 27 original coordinate-frame images. -/
theorem generatedSeventh_spatial_frame_orbit_card :
    Nat.card (MulAction.orbit generatedSeventhSpatialStabilizer
      (leechReduction (leechCoordinateFrameLattice 0))) = 27 := by
  let : Finite LeechModTwo := Finite.of_injective
    leechHyperbolicCoordinates leechHyperbolicCoordinates.injective
  have hlo := Nat.card_le_card_of_injective generatedSeventhFrameOrbitWitness (by
    intro i j h
    exact generatedSeventhFrameOrbitTarget_injective (congrArg Subtype.val h))
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at hlo
  exact Nat.le_antisymm generatedSeventh_spatial_frame_orbit_card_le hlo

/-- The full actual seventh spatial frame stabilizer has exactly 5898240 elements. -/
theorem generatedSeventh_spatial_frame_stabilizer_card :
    Nat.card (MulAction.stabilizer generatedSeventhSpatialStabilizer
      (leechReduction (leechCoordinateFrameLattice 0))) = 5898240 := by
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup
    generatedSeventhSpatialStabilizer (leechReduction (leechCoordinateFrameLattice 0)))
  rw [Nat.card_prod, generatedSeventh_spatial_frame_orbit_card,
    generatedSeventhSpatialStabilizer_card] at h
  omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
