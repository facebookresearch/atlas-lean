/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingSixteenClassTransportCoordinates

/-! A whole actual odd-to-octad transition retaining its positive first root. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The genuine full source transporter also transports the indicated positive first axis. -/
theorem generatedFeasibleSixteenOddOctad_rooted_transporter :
    ∃ h : H,
      rhoLocal h
        (sExtra (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 6) generatedOddAxis)) =
          sExtra (conwayShortAxis (Sum.inr (Sum.inl (generatedOctadBasisOctad, 0))) 0) ∧
      rhoLocal h (conwayShortAxis (Sum.inl (0, generatedFeasibleSixteenOddMiddlePair)) 0) =
        conwayShortAxis (Sum.inl (0, generatedFeasibleSixteenOddFinalPair)) 0 := by
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
  let F := localFiberIncl q * f
  have hF : localGriessRepresentation F x = z := by
    change rhoLocal (inclQ q * localFiberIntoH f) x = z
    rw [map_mul]
    exact hq
  have hp : griessShortPermutation F.val.2
      (Sum.inl (0, generatedFeasibleSixteenOddMiddlePair)) =
        Sum.inl (0, generatedFeasibleSixteenOddFinalPair) := by
    change griessShortPermutation (1 * f.val.2) _ = _
    rw [one_mul, hf]
    exact generatedFeasibleSixteenOddFrame_first_label
  have hx : (griessConwayEncode x).2.1
      (Sum.inl (0, generatedFeasibleSixteenOddMiddlePair)) = 1 := by
    rw [generatedAxisGlobalOddRoot06PositiveShort_actual,
      generatedFeasibleSixteenOddMiddle_output_coefficient, Rat.cast_one]
  have hz : (griessConwayEncode z).2.1
      (Sum.inl (0, generatedFeasibleSixteenOddFinalPair)) = 1 := by
    rw [generatedAxis_triality_octad_pair_coordinate,
      generatedFeasibleSixteenOddFinalPair_coordinates]
    have hmask : griessOctadSignMask generatedOctadBasisOctad 0 = 0 := by
      simp [griessOctadSignMask, trialityEvenMask, trialityBitWeight8]
    have h8 : (0xff00 : ℕ).testBit 8 = true := by decide
    have h10 : (0xff00 : ℕ).testBit 10 = true := by decide
    simp only [griessShortVector, griessShortIntegral,
      generatedOctadBasisOctad_mask, hmask, Nat.zero_testBit,
      Bool.false_eq_true, ite_false, ite_true]
    norm_num
    rw [h8, h10]
    norm_num
    have hs : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
    field_simp
    nlinarith
  have hphase := generatedFeasibleSixteen_phase_from_coefficient F x z _ _ hp hF
    1 (by norm_num) hx hz
  refine ⟨localFiberIntoH F, hF, ?_⟩
  change localGriessRepresentation F _ = _
  rw [generatedAxis_localFiber_image, hp, hphase, zero_add]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
