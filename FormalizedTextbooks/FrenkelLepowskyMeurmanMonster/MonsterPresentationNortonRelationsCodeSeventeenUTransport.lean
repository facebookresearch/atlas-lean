/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeSeventeenUPackets

/-! The actual Norton operator transports the whole original code-seventeen mixed candidate. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Every original inverse short unit has its complete signed inverse-U forward image. -/
theorem monsterNortonCodeSeventeenShortU_unit (p : Fin 8 × Fin 32) :
    (y555NortonActualU⁻¹).val
      (monsterNortonPureShort (monsterNortonCodeSeventeenInverseShortIndex p)) =
        qSign (monsterNortonCodeSeventeenShortUPhase p.1 p.2) •
          monsterNortonPureShort (monsterNortonCodeSeventeenForwardShortIndex
            (monsterNortonCodeSeventeenShortUOutput p)) := by
  rw [monsterNortonPureShort, monsterNortonCodeSeventeenShortU_actual]
  apply (Function.LeftInverse.injective griessConwayDecode_encode)
  rw [griessConwayEncode_decode _ (by intros; rfl)]
  rw [show griessConwayEncode
      (qSign (monsterNortonCodeSeventeenShortUPhase p.1 p.2) •
        monsterNortonPureShort (monsterNortonCodeSeventeenForwardShortIndex
          (monsterNortonCodeSeventeenShortUOutput p))) =
      qSign (monsterNortonCodeSeventeenShortUPhase p.1 p.2) •
        griessConwayEncode (monsterNortonPureShort (monsterNortonCodeSeventeenForwardShortIndex
          (monsterNortonCodeSeventeenShortUOutput p))) from griessConwayEncodeLinear.map_smul _ _]
  rw [monsterNortonPureShort, griessConwayEncode_decode _ (by intros; rfl)]
  simp only [Prod.smul_mk, smul_zero]

/-- The entire inverse short packet maps to the entire forward packet, with all phases retained. -/
theorem monsterNortonCodeSeventeenShort_inverse :
    (y555NortonActualU⁻¹).val monsterNortonCodeSeventeenInverseShort =
      monsterNortonCodeSeventeenForwardShort := by
  rw [monsterNortonCodeSeventeenInverseShort, map_sum]
  have ht (p : Fin 8 × Fin 32) :
      (y555NortonActualU⁻¹).val
        (((monsterNortonCodeSeventeenInverseShortCoefficient p.1 p.2 : ℝ) / 32) •
          monsterNortonPureShort (monsterNortonCodeSeventeenInverseShortIndex p)) =
        ((monsterNortonCodeSeventeenForwardShortCoefficient
          (monsterNortonCodeSeventeenShortUOutput p).1
          (monsterNortonCodeSeventeenShortUOutput p).2 : ℝ) / 32) •
            monsterNortonPureShort (monsterNortonCodeSeventeenForwardShortIndex
              (monsterNortonCodeSeventeenShortUOutput p)) := by
    rw [map_smul, monsterNortonCodeSeventeenShortU_unit, smul_smul]
    congr 1
    have h := congrArg (fun n : ℤ => (n : ℝ) / 32)
      (monsterNortonCodeSeventeenShortU_coefficient p)
    simp only [Int.cast_mul, nortonUIntegerSign_real] at h
    linear_combination h
  simp_rw [ht]
  rw [monsterNortonCodeSeventeenForwardShort]
  exact Fintype.sum_equiv
    (Equiv.ofBijective monsterNortonCodeSeventeenShortUOutput
      monsterNortonCodeSeventeenShortUOutput_bijective) _ _ (fun _ => rfl)

/-- The actual Norton operator sends the complete normalized forward short part to the inverse. -/
theorem monsterNortonCodeSeventeenShort_forward :
    y555NortonActualU.val monsterNortonCodeSeventeenForwardShort =
      monsterNortonCodeSeventeenInverseShort := by
  have h := congrArg (fun x : GriessSpace => y555NortonActualU.val x)
    monsterNortonCodeSeventeenShort_inverse
  change y555NortonActualU.val
    (y555NortonActualU.val.symm monsterNortonCodeSeventeenInverseShort) =
      y555NortonActualU.val monsterNortonCodeSeventeenForwardShort at h
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- Full actual spin and physical transport identifies the complete normalized tensor part. -/
theorem monsterNortonCodeSeventeenTensor_forward :
    y555NortonActualU.val monsterNortonCodeSeventeenForwardTensor =
      monsterNortonCodeSeventeenInverseTensor := by
  rw [monsterNortonCodeSeventeenForwardTensor, map_smul, ← monsterNortonULocal_generated]
  change (1 / (32 * Real.sqrt 2) : ℝ) • localGriessRepresentation monsterNortonUFiber
    (monsterNortonTensorLift (conwayTensorCoordinates
      (nortonUIntegerEmbed monsterNortonCodeSeventeenForwardSpinInteger ⊗ₜ[ℝ]
        (fun j => (monsterNortonCodeSeventeenForwardLeech j : ℝ))))) = _
  rw [monsterNortonLocal_tensor_product_actual, monsterNortonCodeSeventeenSpin_transport,
    monsterNortonCodeSeventeenLeech_transport]
  rfl

/-- The literal seven-factor original Norton word sends the whole forward candidate to inverse. -/
theorem monsterNortonCodeSeventeenU_transport :
    y555NortonActualU.val monsterNortonCodeSeventeenForwardPacket =
      monsterNortonCodeSeventeenInversePacket := by
  rw [monsterNortonCodeSeventeenForwardPacket_parts, map_add,
    monsterNortonCodeSeventeenShort_forward,
    monsterNortonCodeSeventeenTensor_forward, ← monsterNortonCodeSeventeenInversePacket_parts]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
