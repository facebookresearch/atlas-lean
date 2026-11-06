/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeNineteenUPackets

/-! The actual Norton operator transports the whole original code-nineteen mixed candidate. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Every original inverse short unit has its complete signed inverse-U forward image. -/
theorem monsterNortonCodeNineteenShortU_unit (p : Fin 8 × Fin 32) :
    (y555NortonActualU⁻¹).val
      (monsterNortonPureShort (monsterNortonCodeNineteenInverseShortIndex p)) =
        qSign (monsterNortonCodeNineteenShortUPhase p.1 p.2) •
          monsterNortonPureShort (monsterNortonCodeNineteenForwardShortIndex
            (monsterNortonCodeNineteenShortUOutput p)) := by
  rw [monsterNortonPureShort, monsterNortonCodeNineteenShortU_actual]
  apply (Function.LeftInverse.injective griessConwayDecode_encode)
  rw [griessConwayEncode_decode _ (by intros; rfl)]
  rw [show griessConwayEncode
      (qSign (monsterNortonCodeNineteenShortUPhase p.1 p.2) •
        monsterNortonPureShort (monsterNortonCodeNineteenForwardShortIndex
          (monsterNortonCodeNineteenShortUOutput p))) =
      qSign (monsterNortonCodeNineteenShortUPhase p.1 p.2) •
        griessConwayEncode (monsterNortonPureShort (monsterNortonCodeNineteenForwardShortIndex
          (monsterNortonCodeNineteenShortUOutput p))) from griessConwayEncodeLinear.map_smul _ _]
  rw [monsterNortonPureShort, griessConwayEncode_decode _ (by intros; rfl)]
  simp only [Prod.smul_mk, smul_zero]

/-- The entire inverse short packet maps to the entire forward packet, with all phases retained. -/
theorem monsterNortonCodeNineteenShort_inverse :
    (y555NortonActualU⁻¹).val monsterNortonCodeNineteenInverseShort =
      monsterNortonCodeNineteenForwardShort := by
  rw [monsterNortonCodeNineteenInverseShort, map_sum]
  have ht (p : Fin 8 × Fin 32) :
      (y555NortonActualU⁻¹).val
        (((monsterNortonCodeNineteenInverseShortCoefficient p.1 p.2 : ℝ) / 32) •
          monsterNortonPureShort (monsterNortonCodeNineteenInverseShortIndex p)) =
        ((monsterNortonCodeNineteenForwardShortCoefficient
          (monsterNortonCodeNineteenShortUOutput p).1
          (monsterNortonCodeNineteenShortUOutput p).2 : ℝ) / 32) •
            monsterNortonPureShort (monsterNortonCodeNineteenForwardShortIndex
              (monsterNortonCodeNineteenShortUOutput p)) := by
    rw [map_smul, monsterNortonCodeNineteenShortU_unit, smul_smul]
    congr 1
    have h := congrArg (fun n : ℤ => (n : ℝ) / 32)
      (monsterNortonCodeNineteenShortU_coefficient p)
    simp only [Int.cast_mul, nortonUIntegerSign_real] at h
    linear_combination h
  simp_rw [ht]
  rw [monsterNortonCodeNineteenForwardShort]
  exact Fintype.sum_equiv
    (Equiv.ofBijective monsterNortonCodeNineteenShortUOutput
      monsterNortonCodeNineteenShortUOutput_bijective) _ _ (fun _ => rfl)

/-- The actual Norton operator sends the complete normalized forward short part to the inverse. -/
theorem monsterNortonCodeNineteenShort_forward :
    y555NortonActualU.val monsterNortonCodeNineteenForwardShort =
      monsterNortonCodeNineteenInverseShort := by
  have h := congrArg (fun x : GriessSpace => y555NortonActualU.val x)
    monsterNortonCodeNineteenShort_inverse
  change y555NortonActualU.val
    (y555NortonActualU.val.symm monsterNortonCodeNineteenInverseShort) =
      y555NortonActualU.val monsterNortonCodeNineteenForwardShort at h
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- Full actual spin and physical transport identifies the complete normalized tensor part. -/
theorem monsterNortonCodeNineteenTensor_forward :
    y555NortonActualU.val monsterNortonCodeNineteenForwardTensor =
      monsterNortonCodeNineteenInverseTensor := by
  rw [monsterNortonCodeNineteenForwardTensor, map_smul, ← monsterNortonULocal_generated]
  change (1 / (32 * Real.sqrt 2) : ℝ) • localGriessRepresentation monsterNortonUFiber
    (monsterNortonTensorLift (conwayTensorCoordinates
      (nortonUIntegerEmbed monsterNortonCodeNineteenForwardSpinInteger ⊗ₜ[ℝ]
        (fun j => (monsterNortonCodeNineteenForwardLeech j : ℝ))))) = _
  rw [monsterNortonLocal_tensor_product_actual, monsterNortonCodeNineteenSpin_transport,
    monsterNortonCodeNineteenLeech_transport]
  rfl

/-- The literal seven-factor original Norton word sends the whole forward candidate to inverse. -/
theorem monsterNortonCodeNineteenU_transport :
    y555NortonActualU.val monsterNortonCodeNineteenForwardPacket =
      monsterNortonCodeNineteenInversePacket := by
  rw [monsterNortonCodeNineteenForwardPacket_parts, map_add, monsterNortonCodeNineteenShort_forward,
    monsterNortonCodeNineteenTensor_forward, ← monsterNortonCodeNineteenInversePacket_parts]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
