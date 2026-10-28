/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeFiveUPackets

/-! The actual Norton operator transports the whole original code-five mixed candidate. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Every original inverse short unit has its complete signed inverse-U forward image. -/
theorem monsterNortonCodeFiveShortU_unit (p : Fin 8 × Fin 32) :
    (y555NortonActualU⁻¹).val
      (monsterNortonPureShort (monsterNortonCodeFiveInverseShortIndex p)) =
        qSign (monsterNortonCodeFiveShortUPhase p.1 p.2) •
          monsterNortonPureShort (monsterNortonCodeFiveForwardShortIndex
            (monsterNortonCodeFiveShortUOutput p)) := by
  rw [monsterNortonPureShort, monsterNortonCodeFiveShortU_actual]
  apply (Function.LeftInverse.injective griessConwayDecode_encode)
  rw [griessConwayEncode_decode _ (by intros; rfl)]
  rw [show griessConwayEncode
      (qSign (monsterNortonCodeFiveShortUPhase p.1 p.2) •
        monsterNortonPureShort (monsterNortonCodeFiveForwardShortIndex
          (monsterNortonCodeFiveShortUOutput p))) =
      qSign (monsterNortonCodeFiveShortUPhase p.1 p.2) •
        griessConwayEncode (monsterNortonPureShort (monsterNortonCodeFiveForwardShortIndex
          (monsterNortonCodeFiveShortUOutput p))) from griessConwayEncodeLinear.map_smul _ _]
  rw [monsterNortonPureShort, griessConwayEncode_decode _ (by intros; rfl)]
  simp only [Prod.smul_mk, smul_zero]

/-- The entire inverse short packet maps to the entire forward packet, with all phases retained. -/
theorem monsterNortonCodeFiveShort_inverse :
    (y555NortonActualU⁻¹).val monsterNortonCodeFiveInverseShort =
      monsterNortonCodeFiveForwardShort := by
  rw [monsterNortonCodeFiveInverseShort, map_sum]
  have ht (p : Fin 8 × Fin 32) :
      (y555NortonActualU⁻¹).val
        (((monsterNortonCodeFiveInverseShortCoefficient p.1 p.2 : ℝ) / 32) •
          monsterNortonPureShort (monsterNortonCodeFiveInverseShortIndex p)) =
        ((monsterNortonCodeFiveForwardShortCoefficient
          (monsterNortonCodeFiveShortUOutput p).1
          (monsterNortonCodeFiveShortUOutput p).2 : ℝ) / 32) •
            monsterNortonPureShort (monsterNortonCodeFiveForwardShortIndex
              (monsterNortonCodeFiveShortUOutput p)) := by
    rw [map_smul, monsterNortonCodeFiveShortU_unit, smul_smul]
    congr 1
    have h := congrArg (fun n : ℤ => (n : ℝ) / 32)
      (monsterNortonCodeFiveShortU_coefficient p)
    simp only [Int.cast_mul, nortonUIntegerSign_real] at h
    linear_combination h
  simp_rw [ht]
  rw [monsterNortonCodeFiveForwardShort]
  exact Fintype.sum_equiv
    (Equiv.ofBijective monsterNortonCodeFiveShortUOutput
      monsterNortonCodeFiveShortUOutput_bijective) _ _ (fun _ => rfl)

/-- The actual Norton operator sends the complete normalized forward short part to the inverse. -/
theorem monsterNortonCodeFiveShort_forward :
    y555NortonActualU.val monsterNortonCodeFiveForwardShort =
      monsterNortonCodeFiveInverseShort := by
  have h := congrArg (fun x : GriessSpace => y555NortonActualU.val x)
    monsterNortonCodeFiveShort_inverse
  change y555NortonActualU.val
    (y555NortonActualU.val.symm monsterNortonCodeFiveInverseShort) =
      y555NortonActualU.val monsterNortonCodeFiveForwardShort at h
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- Full actual spin and physical transport identifies the complete normalized tensor part. -/
theorem monsterNortonCodeFiveTensor_forward :
    y555NortonActualU.val monsterNortonCodeFiveForwardTensor =
      monsterNortonCodeFiveInverseTensor := by
  rw [monsterNortonCodeFiveForwardTensor, map_smul, ← monsterNortonULocal_generated]
  change (1 / (32 * Real.sqrt 2) : ℝ) • localGriessRepresentation monsterNortonUFiber
    (monsterNortonTensorLift (conwayTensorCoordinates
      (nortonUIntegerEmbed monsterNortonCodeFiveForwardSpinInteger ⊗ₜ[ℝ]
        (fun j => (monsterNortonCodeFiveForwardLeech j : ℝ))))) = _
  rw [monsterNortonLocal_tensor_product_actual, monsterNortonCodeFiveSpin_transport,
    monsterNortonCodeFiveLeech_transport]
  rfl

/-- The literal seven-factor original Norton word sends the whole forward candidate to inverse. -/
theorem monsterNortonCodeFiveU_transport :
    y555NortonActualU.val monsterNortonCodeFiveForwardPacket =
      monsterNortonCodeFiveInversePacket := by
  rw [monsterNortonCodeFiveForwardPacket_parts, map_add, monsterNortonCodeFiveShort_forward,
    monsterNortonCodeFiveTensor_forward, ← monsterNortonCodeFiveInversePacket_parts]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
