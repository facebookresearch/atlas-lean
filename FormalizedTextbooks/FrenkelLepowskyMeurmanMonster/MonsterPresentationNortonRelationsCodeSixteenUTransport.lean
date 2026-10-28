/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeSixteenUPackets

/-! The actual Norton operator transports the whole original code-sixteen mixed candidate. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Every original inverse short unit has its complete signed inverse-U forward image. -/
theorem monsterNortonCodeSixteenShortU_unit (p : Fin 8 × Fin 32) :
    (y555NortonActualU⁻¹).val
      (monsterNortonPureShort (monsterNortonCodeSixteenInverseShortIndex p)) =
        qSign (monsterNortonCodeSixteenShortUPhase p.1 p.2) •
          monsterNortonPureShort (monsterNortonCodeSixteenForwardShortIndex
            (monsterNortonCodeSixteenShortUOutput p)) := by
  rw [monsterNortonPureShort, monsterNortonCodeSixteenShortU_actual]
  apply (Function.LeftInverse.injective griessConwayDecode_encode)
  rw [griessConwayEncode_decode _ (by intros; rfl)]
  rw [show griessConwayEncode
      (qSign (monsterNortonCodeSixteenShortUPhase p.1 p.2) •
        monsterNortonPureShort (monsterNortonCodeSixteenForwardShortIndex
          (monsterNortonCodeSixteenShortUOutput p))) =
      qSign (monsterNortonCodeSixteenShortUPhase p.1 p.2) •
        griessConwayEncode (monsterNortonPureShort (monsterNortonCodeSixteenForwardShortIndex
          (monsterNortonCodeSixteenShortUOutput p))) from griessConwayEncodeLinear.map_smul _ _]
  rw [monsterNortonPureShort, griessConwayEncode_decode _ (by intros; rfl)]
  simp only [Prod.smul_mk, smul_zero]

/-- The entire inverse short packet maps to the entire forward packet, with all phases retained. -/
theorem monsterNortonCodeSixteenShort_inverse :
    (y555NortonActualU⁻¹).val monsterNortonCodeSixteenInverseShort =
      monsterNortonCodeSixteenForwardShort := by
  rw [monsterNortonCodeSixteenInverseShort, map_sum]
  have ht (p : Fin 8 × Fin 32) :
      (y555NortonActualU⁻¹).val
        (((monsterNortonCodeSixteenInverseShortCoefficient p.1 p.2 : ℝ) / 32) •
          monsterNortonPureShort (monsterNortonCodeSixteenInverseShortIndex p)) =
        ((monsterNortonCodeSixteenForwardShortCoefficient
          (monsterNortonCodeSixteenShortUOutput p).1
          (monsterNortonCodeSixteenShortUOutput p).2 : ℝ) / 32) •
            monsterNortonPureShort (monsterNortonCodeSixteenForwardShortIndex
              (monsterNortonCodeSixteenShortUOutput p)) := by
    rw [map_smul, monsterNortonCodeSixteenShortU_unit, smul_smul]
    congr 1
    have h := congrArg (fun n : ℤ => (n : ℝ) / 32)
      (monsterNortonCodeSixteenShortU_coefficient p)
    simp only [Int.cast_mul, nortonUIntegerSign_real] at h
    linear_combination h
  simp_rw [ht]
  rw [monsterNortonCodeSixteenForwardShort]
  exact Fintype.sum_equiv
    (Equiv.ofBijective monsterNortonCodeSixteenShortUOutput
      monsterNortonCodeSixteenShortUOutput_bijective) _ _ (fun _ => rfl)

/-- The actual Norton operator sends the complete normalized forward short part to the inverse. -/
theorem monsterNortonCodeSixteenShort_forward :
    y555NortonActualU.val monsterNortonCodeSixteenForwardShort =
      monsterNortonCodeSixteenInverseShort := by
  have h := congrArg (fun x : GriessSpace => y555NortonActualU.val x)
    monsterNortonCodeSixteenShort_inverse
  change y555NortonActualU.val
    (y555NortonActualU.val.symm monsterNortonCodeSixteenInverseShort) =
      y555NortonActualU.val monsterNortonCodeSixteenForwardShort at h
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- Full actual spin and physical transport identifies the complete normalized tensor part. -/
theorem monsterNortonCodeSixteenTensor_forward :
    y555NortonActualU.val monsterNortonCodeSixteenForwardTensor =
      monsterNortonCodeSixteenInverseTensor := by
  rw [monsterNortonCodeSixteenForwardTensor, map_smul, ← monsterNortonULocal_generated]
  change (1 / (32 * Real.sqrt 2) : ℝ) • localGriessRepresentation monsterNortonUFiber
    (monsterNortonTensorLift (conwayTensorCoordinates
      (nortonUIntegerEmbed monsterNortonCodeSixteenForwardSpinInteger ⊗ₜ[ℝ]
        (fun j => (monsterNortonCodeSixteenForwardLeech j : ℝ))))) = _
  rw [monsterNortonLocal_tensor_product_actual, monsterNortonCodeSixteenSpin_transport,
    monsterNortonCodeSixteenLeech_transport]
  rfl

/-- The literal seven-factor original Norton word sends the whole forward candidate to inverse. -/
theorem monsterNortonCodeSixteenU_transport :
    y555NortonActualU.val monsterNortonCodeSixteenForwardPacket =
      monsterNortonCodeSixteenInversePacket := by
  rw [monsterNortonCodeSixteenForwardPacket_parts, map_add, monsterNortonCodeSixteenShort_forward,
    monsterNortonCodeSixteenTensor_forward, ← monsterNortonCodeSixteenInversePacket_parts]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
