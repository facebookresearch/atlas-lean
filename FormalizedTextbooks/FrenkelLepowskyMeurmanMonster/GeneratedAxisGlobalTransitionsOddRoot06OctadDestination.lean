/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06OctadSourceActual
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06OctadOutgoingCertificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06OctadStandardMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06OctadLiftCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadLocalLift
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalCoverageFirstLayer

/-! A genuine complete original source packet, genuine lattice frame, and original Q sign comparison identify the actual octad destination. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Every original positive short coefficient is the complete exact sparse packet. -/
theorem generatedAxisGlobalOddRoot06PositiveShort_actual (r : GriessShortIndex) :
    (griessConwayEncode
      (sExtra (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 6) generatedOddAxis))).2.1 r =
      (generatedAxisGlobalOddRoot06OctadSparseShortQ r : ℝ) := by
  rw [generatedAxisGlobalOddRoot06PositivePacket_actual]
  change (generatedAxisGlobalOddRoot06PositiveShortQ r : ℝ) = _
  rw [generatedAxisGlobalOddRoot06PositiveShort_sparse]

/-- The entire actual positive root-six vector is locally carried to the original standard-octad axis. -/
theorem generatedAxisGlobalOddRoot06PositiveOctad_transporter :
    ∃ h : H, rhoLocal h
      (sExtra (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 6) generatedOddAxis)) =
        sExtra (conwayShortAxis (Sum.inr (Sum.inl (generatedOctadBasisOctad, 0))) 0) := by
  let x := sExtra (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 6) generatedOddAxis)
  let z := sExtra (conwayShortAxis (Sum.inr (Sum.inl (generatedOctadBasisOctad, 0))) 0)
  obtain ⟨f, hf⟩ := generatedCentral_localFiber_lift generatedAxisGlobalOddRoot06OctadStandardFrameIsometry
  let y := localGriessRepresentation f x
  have hm : (griessConwayEncode y).1 = (griessConwayEncode z).1 := by
    dsimp only [y]
    rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply]
    change conwayMatrixAction f.val.2 (griessConwayEncode x).1 = _
    rw [hf]
    dsimp only [x, z]
    rw [generatedAxisGlobalOddRoot06PositiveStandardProjection_actual,
      generatedAxis_triality_octad_matrix, generatedOctadBasisOctad_mask]
  have htx : (griessConwayEncode x).2.2 = 0 := generatedAxisGlobalOddRoot06PositiveTensor_zero
  have hty : (griessConwayEncode y).2.2 = 0 := by
    dsimp only [y]
    rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply]
    change localTensorRepresentation f (griessConwayEncode x).2.2 = 0
    rw [htx, map_zero]
  have hiz : griessProd z z = (64 : ℝ) • z := generatedAxis_triality_short_square _ _
  have hix : griessProd x x = (64 : ℝ) • x := by
    dsimp only [x]
    rw [← sExtra_preserves_griessProd, ← rhoLocal_product]
    have hi : griessProd generatedOddAxis generatedOddAxis = (64 : ℝ) • generatedOddAxis := by
      rw [generatedOddAxis]
      exact generatedAxis_triality_short_square _ _
    rw [hi, map_smul, map_smul]
  have hiy : griessProd y y = (64 : ℝ) • y := by
    dsimp only [y]
    rw [← localGriessRepresentation_product, hix, map_smul]
  obtain ⟨q, hq⟩ := generatedOctad_idempotents_Q_related y z hm hty
    (generatedAxis_triality_octad_tensor_zero_all generatedOctadBasisOctad 0 0)
    (generatedAxisGlobalOddRoot06OctadLift_supported_square x f hf
      generatedAxisGlobalOddRoot06PositiveShort_actual)
    (generatedAxis_triality_octad_supported_square generatedOctadBasisOctad 0 0)
    (generatedAxisGlobalOddRoot06OctadLift_unsupported_zero x f hf
      generatedAxisGlobalOddRoot06PositiveShort_actual)
    (generatedAxis_triality_octad_unsupported_zero generatedOctadBasisOctad 0 0)
    (fun r hr => by rw [hm]; exact generatedAxisE8_supported_pairing_four generatedOctadBasisOctad 0 0 r hr)
    (generatedAxis_raw_idempotent_short y hiy)
    (generatedAxis_raw_idempotent_short z hiz)
  refine ⟨inclQ q * localFiberIntoH f, ?_⟩
  rw [map_mul]
  exact hq

/-- The positive original root-six transition lies in the actual octad-image local class. -/
theorem generatedAxisGlobalOddRoot06_positive_destination :
    Quotient.mk (MulAction.orbitRel H GriessSpace)
      (sExtra (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 6) generatedOddAxis)) =
        generatedAxisOctadDestination := by
  have he : Quotient.mk (MulAction.orbitRel H GriessSpace)
      (sExtra (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 6) generatedOddAxis)) =
    Quotient.mk (MulAction.orbitRel H GriessSpace)
      (sExtra (conwayShortAxis (Sum.inr (Sum.inl (generatedOctadBasisOctad, 0))) 0)) :=
    (generatedAxis_local_class_eq_iff _ _).mpr generatedAxisGlobalOddRoot06PositiveOctad_transporter
  exact he.trans ((generatedAxis_triality_octad_class_iff _ _).mpr ⟨generatedOctadBasisOctad, 0, rfl⟩)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
