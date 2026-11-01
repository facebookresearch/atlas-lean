/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTenUPackets

/-! The actual Norton operator transports the whole original basis-ten mixed candidate. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Every original inverse short unit has its complete signed inverse-U forward image. -/
theorem monsterNortonCodeTenShortU_unit (p : Fin 2 × Fin 128) :
    (y555NortonActualU⁻¹).val
      (monsterNortonPureShort (monsterNortonCodeTenInverseShortIndex p)) =
        qSign (monsterNortonCodeTenShortUPhase p.1 p.2) •
          monsterNortonPureShort (monsterNortonCodeTenForwardShortIndex
            (monsterNortonCodeTenShortUOutput p)) := by
  rw [monsterNortonPureShort, monsterNortonCodeTenShortU_actual]
  apply (Function.LeftInverse.injective griessConwayDecode_encode)
  rw [griessConwayEncode_decode _ (by intros; rfl)]
  rw [show griessConwayEncode
      (qSign (monsterNortonCodeTenShortUPhase p.1 p.2) •
        monsterNortonPureShort (monsterNortonCodeTenForwardShortIndex
          (monsterNortonCodeTenShortUOutput p))) =
      qSign (monsterNortonCodeTenShortUPhase p.1 p.2) •
        griessConwayEncode (monsterNortonPureShort (monsterNortonCodeTenForwardShortIndex
          (monsterNortonCodeTenShortUOutput p))) from griessConwayEncodeLinear.map_smul _ _]
  rw [monsterNortonPureShort, griessConwayEncode_decode _ (by intros; rfl)]
  simp only [Prod.smul_mk, smul_zero]

/-- The entire inverse short packet maps to the entire forward packet, with all phases retained. -/
theorem monsterNortonCodeTenShort_inverse :
    (y555NortonActualU⁻¹).val monsterNortonCodeTenInverseShort =
      monsterNortonCodeTenForwardShort := by
  rw [monsterNortonCodeTenInverseShort, map_sum]
  have ht (p : Fin 2 × Fin 128) :
      (y555NortonActualU⁻¹).val
        (((monsterNortonCodeTenInverseShortCoefficient p.1 p.2 : ℝ) / 32) •
          monsterNortonPureShort (monsterNortonCodeTenInverseShortIndex p)) =
        ((monsterNortonCodeTenForwardShortCoefficient
          (monsterNortonCodeTenShortUOutput p).1
          (monsterNortonCodeTenShortUOutput p).2 : ℝ) / 32) •
            monsterNortonPureShort (monsterNortonCodeTenForwardShortIndex
              (monsterNortonCodeTenShortUOutput p)) := by
    rw [map_smul, monsterNortonCodeTenShortU_unit, smul_smul]
    congr 1
    have h := congrArg (fun n : ℤ => (n : ℝ) / 32)
      (monsterNortonCodeTenShortU_coefficient p)
    simp only [Int.cast_mul, nortonUIntegerSign_real] at h
    linear_combination h
  simp_rw [ht]
  rw [monsterNortonCodeTenForwardShort]
  exact Fintype.sum_equiv
    (Equiv.ofBijective monsterNortonCodeTenShortUOutput
      monsterNortonCodeTenShortUOutput_bijective) _ _ (fun _ => rfl)

/-- The actual Norton operator sends the complete normalized forward short part to the inverse. -/
theorem monsterNortonCodeTenShort_forward :
    y555NortonActualU.val monsterNortonCodeTenForwardShort =
      monsterNortonCodeTenInverseShort := by
  have h := congrArg (fun x : GriessSpace => y555NortonActualU.val x)
    monsterNortonCodeTenShort_inverse
  change y555NortonActualU.val
    (y555NortonActualU.val.symm monsterNortonCodeTenInverseShort) =
      y555NortonActualU.val monsterNortonCodeTenForwardShort at h
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- Full actual spin and physical transport identifies the complete normalized tensor part. -/
theorem monsterNortonCodeTenTensor_forward :
    y555NortonActualU.val monsterNortonCodeTenForwardTensor =
      monsterNortonCodeTenInverseTensor := by
  rw [monsterNortonCodeTenForwardTensor, map_smul, ← monsterNortonULocal_generated]
  change (1 / (32 * Real.sqrt 2) : ℝ) • localGriessRepresentation monsterNortonUFiber
    (monsterNortonTensorLift (conwayTensorCoordinates
      (nortonUIntegerEmbed monsterNortonCodeTenForwardSpinInteger ⊗ₜ[ℝ]
        (fun j => (monsterNortonCodeTenForwardLeech j : ℝ))))) = _
  rw [monsterNortonLocal_tensor_product_actual, monsterNortonCodeTenSpin_transport,
    monsterNortonCodeTenLeech_transport]
  rfl

/-- The literal seven-factor original Norton word sends the whole forward candidate to inverse. -/
theorem monsterNortonCodeTenU_transport :
    y555NortonActualU.val monsterNortonCodeTenForwardPacket =
      monsterNortonCodeTenInversePacket := by
  rw [monsterNortonCodeTenForwardPacket_parts, map_add, monsterNortonCodeTenShort_forward,
    monsterNortonCodeTenTensor_forward, ← monsterNortonCodeTenInversePacket_parts]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
