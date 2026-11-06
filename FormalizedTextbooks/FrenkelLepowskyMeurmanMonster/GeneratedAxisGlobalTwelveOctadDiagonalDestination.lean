/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveOctadDiagonalFrame
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveOctadFamily
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadQComparison
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8Pairing
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFamilyOrbits
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerLocalLift
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadLocalCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadAxisData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadPhaseExact
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalProductInvariance
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadLocalLift

/-! The octad-diagonal transition vector is locally conjugate to the listed Octad
representative, and its binary root is the second root of the binary octad forest. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The candidate coefficient at every transition support label. -/
theorem generatedAxisGlobalTwelveOctadDiagonalXShortQ_source (k : Fin 120) :
    generatedAxisGlobalTwelveOctadDiagonalXShortQ (generatedAxisGlobalTwelveOctadDiagonalXLabel k) = generatedAxisGlobalTwelveOctadDiagonalXCoeff k := by
  unfold generatedAxisGlobalTwelveOctadDiagonalXShortQ
  rw [generatedAxisGlobalTwelveOctadDiagonalXSource_roundtrip]

/-- Every actual lift of the frame gives unit coefficients on the octad-three support. -/
theorem generatedAxisGlobalTwelveOctadDiagonalLift_supported_square (f : localFiberSubgroup)
    (hf : f.val.2 = generatedAxisGlobalTwelveOctadDiagonalFrameIsometry)
    (r : GriessShortIndex) (hr : generatedOctadShortSupport generatedOctadBasisOctad r) :
    (griessConwayEncode (localGriessRepresentation f generatedAxisGlobalTwelveOctadDiagonalX)).2.1 r ^ 2 = 1 := by
  obtain ⟨k, rfl⟩ := generatedAxisGlobalTwelveOctadDiagonalXTarget_coverage r hr
  have hp : griessShortPermutation f.val.2 (generatedAxisGlobalTwelveOctadDiagonalXLabel k) = generatedAxisGlobalTwelveOctadDiagonalXTarget k := by
    rw [hf]
    exact generatedAxisGlobalTwelveOctadDiagonalShortPermutation_frame k
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply, ← hp]
  change (localShortOperator f (griessConwayEncode generatedAxisGlobalTwelveOctadDiagonalX).2.1
    (griessShortPermutation f.val.2 (generatedAxisGlobalTwelveOctadDiagonalXLabel k))) ^ 2 = 1
  rw [localShortOperator_image, generatedAxisGlobalTwelveOctadDiagonalXShort_actual, generatedAxisGlobalTwelveOctadDiagonalXShortQ_source,
    mul_pow, pow_two, qSign_sq, one_mul]
  exact_mod_cast (generatedAxisGlobalTwelveOctadDiagonalFrame_units k).2

/-- An actual lift of the frame creates no coordinate outside the octad-three support. -/
theorem generatedAxisGlobalTwelveOctadDiagonalLift_unsupported_zero (f : localFiberSubgroup)
    (hf : f.val.2 = generatedAxisGlobalTwelveOctadDiagonalFrameIsometry)
    (r : GriessShortIndex) (hr : ¬ generatedOctadShortSupport generatedOctadBasisOctad r) :
    (griessConwayEncode (localGriessRepresentation f generatedAxisGlobalTwelveOctadDiagonalX)).2.1 r = 0 := by
  obtain ⟨s, rfl⟩ := (griessShortPermutation f.val.2).surjective r
  have hz : generatedAxisGlobalTwelveOctadDiagonalXShortQ s = 0 := by
    have hn : generatedAxisGlobalTwelveOctadDiagonalXSource s = none := by
      cases h : generatedAxisGlobalTwelveOctadDiagonalXSource s with
      | none => rfl
      | some k =>
        have hk := generatedAxisGlobalTwelveOctadDiagonalXSource_sound s k h
        subst s
        have hperm : griessShortPermutation f.val.2 (generatedAxisGlobalTwelveOctadDiagonalXLabel k) = generatedAxisGlobalTwelveOctadDiagonalXTarget k := by
          rw [hf]
          exact generatedAxisGlobalTwelveOctadDiagonalShortPermutation_frame k
        rw [hperm] at hr
        exact False.elim (hr (generatedAxisGlobalTwelveOctadDiagonalXTarget_supported k))
    simp only [generatedAxisGlobalTwelveOctadDiagonalXShortQ, hn]
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply]
  change localShortOperator f _ (griessShortPermutation f.val.2 s) = 0
  rw [localShortOperator_image, generatedAxisGlobalTwelveOctadDiagonalXShort_actual, hz, Rat.cast_zero, mul_zero]

/-- The entire actual octad-diagonal transition vector is locally carried to the listed Octad
representative. -/
theorem generatedAxisGlobalTwelveOctadDiagonal_transporter :
    ∃ h : H, rhoLocal h generatedAxisGlobalTwelveOctadDiagonalX = generatedOctadLocalAxis 0 0 := by
  let x := generatedAxisGlobalTwelveOctadDiagonalX
  let z := generatedOctadLocalAxis 0 0
  obtain ⟨f, hf⟩ := generatedCentral_localFiber_lift generatedAxisGlobalTwelveOctadDiagonalFrameIsometry
  let y := localGriessRepresentation f x
  have hm : (griessConwayEncode y).1 = (griessConwayEncode z).1 := by
    dsimp only [y]
    rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply]
    change conwayMatrixAction f.val.2 (griessConwayEncode generatedAxisGlobalTwelveOctadDiagonalX).1 =
      (griessConwayEncode
        (sExtra (conwayShortAxis (Sum.inr (Sum.inl (generatedOctadBasisOctad, 0))) 0))).1
    rw [hf, generatedAxisGlobalTwelveOctadDiagonalFrame_matrix, generatedAxis_triality_octad_matrix,
      generatedOctadBasisOctad_mask]
  have htx : (griessConwayEncode x).2.2 = 0 := generatedAxisGlobalTwelveOctadDiagonalXTensor_actual
  have hty : (griessConwayEncode y).2.2 = 0 := by
    dsimp only [y]
    rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply]
    change localTensorRepresentation f (griessConwayEncode x).2.2 = 0
    rw [htx, map_zero]
  have hiz : griessProd z z = (64 : ℝ) • z := generatedAxis_triality_short_square _ _
  have hix : griessProd x x = (64 : ℝ) • x := by
    change griessProd (sExtra (rhoLocal generatedAxisGlobalTwelveOctadDiagonalLocal z))
      (sExtra (rhoLocal generatedAxisGlobalTwelveOctadDiagonalLocal z)) = (64 : ℝ) • sExtra (rhoLocal generatedAxisGlobalTwelveOctadDiagonalLocal z)
    rw [← sExtra_preserves_griessProd, ← rhoLocal_product, hiz, map_smul, map_smul]
  have hiy : griessProd y y = (64 : ℝ) • y := by
    dsimp only [y]
    rw [← localGriessRepresentation_product, hix, map_smul]
  obtain ⟨q, hq⟩ := generatedOctad_idempotents_Q_related y z hm hty
    (generatedAxis_triality_octad_tensor_zero_all generatedOctadBasisOctad 0 0)
    (generatedAxisGlobalTwelveOctadDiagonalLift_supported_square f hf)
    (generatedAxis_triality_octad_supported_square generatedOctadBasisOctad 0 0)
    (generatedAxisGlobalTwelveOctadDiagonalLift_unsupported_zero f hf)
    (generatedAxis_triality_octad_unsupported_zero generatedOctadBasisOctad 0 0)
    (fun r hr => by
      rw [hm]
      exact generatedAxisE8_supported_pairing_four generatedOctadBasisOctad 0 0 r hr)
    (generatedAxis_raw_idempotent_short y hiy)
    (generatedAxis_raw_idempotent_short z hiz)
  refine ⟨inclQ q * localFiberIntoH f, ?_⟩
  rw [map_mul]
  exact hq

/-- The octad-diagonal transition lies in the local class of the listed Octad representative. -/
theorem generatedAxisGlobalTwelveOctadDiagonal_class :
    generatedAxisGlobalTwelveOctadClass generatedAxisGlobalTwelveOctadDiagonalX =
      generatedAxisGlobalTwelveOctadClass (generatedOctadLocalAxis 0 0) :=
  (generatedAxis_local_class_eq_iff _ _).mpr generatedAxisGlobalTwelveOctadDiagonal_transporter

/-- The Conway projection of the inverse transition is the second root word. -/
theorem generatedAxisGlobalTwelveOctadDiagonalLocal_projection_inv :
    projH generatedAxisGlobalTwelveOctadDiagonalLocal⁻¹ =
      generatedAxisGlobalTwelveOctadLetterWord (generatedAxisGlobalTwelveOctadRootWord 1) := by
  have hf : generatedAxisGlobalTwelveOctadDiagonalFiber = xiSpinLocalFiber⁻¹ * (monsterSourcePermutationFiber 1)⁻¹ := by
    simp [generatedAxisGlobalTwelveOctadDiagonalFiber, generatedAxisGlobalTwelveOctadDiagonalWord, generatedAxisGlobalOddSourceFiberLetter,
      generatedAxisGlobalOddSourceBaseFiber]
  have hinv : generatedAxisGlobalTwelveOctadDiagonalFiber⁻¹ = monsterSourcePermutationFiber 1 * xiSpinLocalFiber := by
    rw [hf]
    group
  have h17 : generatedAxisGlobalTwelveOctadLetter 17 = omegaOrbitPermutationIsometry 1 := rfl
  have h15 : generatedAxisGlobalTwelveOctadLetter 15 = co1XiIsometry := rfl
  change projH (localFiberIntoH generatedAxisGlobalTwelveOctadDiagonalFiber)⁻¹ = _
  rw [← map_inv, hinv]
  change QuotientGroup.mk' signsSubgroup (omegaOrbitPermutationIsometry 1 * co1XiIsometry) = _
  simp only [generatedAxisGlobalTwelveOctadLetterWord, generatedAxisGlobalTwelveOctadRootWord,
    Matrix.cons_val_one, Matrix.cons_val_zero, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, map_mul, h17, h15]

/-- The binary root of the transition is the second root of the binary octad forest. -/
theorem generatedAxisGlobalTwelveOctadDiagonalLocal_binary_root :
    generatedAxisGlobalBinaryRoot generatedAxisGlobalTwelveOctadDiagonalLocal = generatedAxisGlobalTwelveOctadRootPoint 1 := by
  apply Subtype.ext
  change co1BinaryAction (projH generatedAxisGlobalTwelveOctadDiagonalLocal⁻¹) (toAdd (qQuotHom sourceOmegaQ)) =
    monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalTwelveOctadRootMask 1)
  rw [generatedAxisGlobalTwelveOctadDiagonalLocal_projection_inv, ← generatedAxisGlobalTwelveOctadOmega_decode,
    generatedAxisGlobalTwelveOctadLetterWord_action,
    generatedAxisGlobalTwelveOctadRootWord_certificate]

/-- The explicit octad-diagonal binding: the identity stabilizer element carries the binary root
of the transition to the second forest root, and the transition is locally the Octad
representative. -/
theorem generatedAxisGlobalTwelveOctad_diagonalBound :
    GeneratedAxisGlobalTwelveOctadDiagonalBound := by
  have h1 : ∀ x : generatedAxisGlobalBinaryOrbit, generatedAxisGlobalBinaryAct 1 x = x := by
    intro x
    apply Subtype.ext
    change co1BinaryAction (projH 1) x.val = x.val
    rw [map_one, map_one]
    rfl
  refine ⟨generatedAxisGlobalTwelveOctadDiagonalLocal, 1, one_mem _, ?_, generatedAxisGlobalTwelveOctadDiagonal_class⟩
  rw [h1]
  exact generatedAxisGlobalTwelveOctadDiagonalLocal_binary_root

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
