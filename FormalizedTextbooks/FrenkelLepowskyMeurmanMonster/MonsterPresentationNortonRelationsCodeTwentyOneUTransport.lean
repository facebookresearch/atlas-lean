/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyOneUPackets

/-! The actual Norton operator transports the whole original code-twentyone mixed candidate. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Every original inverse short unit has its complete signed inverse-U forward image. -/
theorem monsterNortonCodeTwentyOneShortU_unit (p : Fin 8 × Fin 32) :
    (y555NortonActualU⁻¹).val
      (monsterNortonPureShort (monsterNortonCodeTwentyOneInverseShortIndex p)) =
        qSign (monsterNortonCodeTwentyOneShortUPhase p.1 p.2) •
          monsterNortonPureShort (monsterNortonCodeTwentyOneForwardShortIndex
            (monsterNortonCodeTwentyOneShortUOutput p)) := by
  rw [monsterNortonPureShort, monsterNortonCodeTwentyOneShortU_actual]
  apply (Function.LeftInverse.injective griessConwayDecode_encode)
  rw [griessConwayEncode_decode _ (by intros; rfl)]
  rw [show griessConwayEncode
      (qSign (monsterNortonCodeTwentyOneShortUPhase p.1 p.2) •
        monsterNortonPureShort (monsterNortonCodeTwentyOneForwardShortIndex
          (monsterNortonCodeTwentyOneShortUOutput p))) =
      qSign (monsterNortonCodeTwentyOneShortUPhase p.1 p.2) •
        griessConwayEncode (monsterNortonPureShort (monsterNortonCodeTwentyOneForwardShortIndex
          (monsterNortonCodeTwentyOneShortUOutput p))) from griessConwayEncodeLinear.map_smul _ _]
  rw [monsterNortonPureShort, griessConwayEncode_decode _ (by intros; rfl)]
  simp only [Prod.smul_mk, smul_zero]

/-- The entire inverse short packet maps to the entire forward packet, with all phases retained. -/
theorem monsterNortonCodeTwentyOneShort_inverse :
    (y555NortonActualU⁻¹).val monsterNortonCodeTwentyOneInverseShort =
      monsterNortonCodeTwentyOneForwardShort := by
  rw [monsterNortonCodeTwentyOneInverseShort, map_sum]
  have ht (p : Fin 8 × Fin 32) :
      (y555NortonActualU⁻¹).val
        (((monsterNortonCodeTwentyOneInverseShortCoefficient p.1 p.2 : ℝ) / 32) •
          monsterNortonPureShort (monsterNortonCodeTwentyOneInverseShortIndex p)) =
        ((monsterNortonCodeTwentyOneForwardShortCoefficient
          (monsterNortonCodeTwentyOneShortUOutput p).1
          (monsterNortonCodeTwentyOneShortUOutput p).2 : ℝ) / 32) •
            monsterNortonPureShort (monsterNortonCodeTwentyOneForwardShortIndex
              (monsterNortonCodeTwentyOneShortUOutput p)) := by
    rw [map_smul, monsterNortonCodeTwentyOneShortU_unit, smul_smul]
    congr 1
    have h := congrArg (fun n : ℤ => (n : ℝ) / 32)
      (monsterNortonCodeTwentyOneShortU_coefficient p)
    simp only [Int.cast_mul, nortonUIntegerSign_real] at h
    linear_combination h
  simp_rw [ht]
  rw [monsterNortonCodeTwentyOneForwardShort]
  exact Fintype.sum_equiv
    (Equiv.ofBijective monsterNortonCodeTwentyOneShortUOutput
      monsterNortonCodeTwentyOneShortUOutput_bijective) _ _ (fun _ => rfl)

/-- The actual Norton operator sends the complete normalized forward short part to the inverse. -/
theorem monsterNortonCodeTwentyOneShort_forward :
    y555NortonActualU.val monsterNortonCodeTwentyOneForwardShort =
      monsterNortonCodeTwentyOneInverseShort := by
  have h := congrArg (fun x : GriessSpace => y555NortonActualU.val x)
    monsterNortonCodeTwentyOneShort_inverse
  change y555NortonActualU.val
    (y555NortonActualU.val.symm monsterNortonCodeTwentyOneInverseShort) =
      y555NortonActualU.val monsterNortonCodeTwentyOneForwardShort at h
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- Full actual spin and physical transport identifies the complete normalized tensor part. -/
theorem monsterNortonCodeTwentyOneTensor_forward :
    y555NortonActualU.val monsterNortonCodeTwentyOneForwardTensor =
      monsterNortonCodeTwentyOneInverseTensor := by
  rw [monsterNortonCodeTwentyOneForwardTensor, map_smul, ← monsterNortonULocal_generated]
  change (1 / (32 * Real.sqrt 2) : ℝ) • localGriessRepresentation monsterNortonUFiber
    (monsterNortonTensorLift (conwayTensorCoordinates
      (nortonUIntegerEmbed monsterNortonCodeTwentyOneForwardSpinInteger ⊗ₜ[ℝ]
        (fun j => (monsterNortonCodeTwentyOneForwardLeech j : ℝ))))) = _
  rw [monsterNortonLocal_tensor_product_actual, monsterNortonCodeTwentyOneSpin_transport,
    monsterNortonCodeTwentyOneLeech_transport]
  rfl

/-- The literal seven-factor original Norton word sends the whole forward candidate to inverse. -/
theorem monsterNortonCodeTwentyOneU_transport :
    y555NortonActualU.val monsterNortonCodeTwentyOneForwardPacket =
      monsterNortonCodeTwentyOneInversePacket := by
  rw [monsterNortonCodeTwentyOneForwardPacket_parts, map_add,
    monsterNortonCodeTwentyOneShort_forward,
    monsterNortonCodeTwentyOneTensor_forward, ← monsterNortonCodeTwentyOneInversePacket_parts]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
