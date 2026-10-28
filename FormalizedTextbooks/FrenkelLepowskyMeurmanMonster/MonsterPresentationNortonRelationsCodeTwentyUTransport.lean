/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyUPackets

/-! The actual Norton operator transports the whole original code-twenty mixed candidate. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Every original inverse short unit has its complete signed inverse-U forward image. -/
theorem monsterNortonCodeTwentyShortU_unit (p : Fin 8 × Fin 32) :
    (y555NortonActualU⁻¹).val
      (monsterNortonPureShort (monsterNortonCodeTwentyInverseShortIndex p)) =
        qSign (monsterNortonCodeTwentyShortUPhase p.1 p.2) •
          monsterNortonPureShort (monsterNortonCodeTwentyForwardShortIndex
            (monsterNortonCodeTwentyShortUOutput p)) := by
  rw [monsterNortonPureShort, monsterNortonCodeTwentyShortU_actual]
  apply (Function.LeftInverse.injective griessConwayDecode_encode)
  rw [griessConwayEncode_decode _ (by intros; rfl)]
  rw [show griessConwayEncode
      (qSign (monsterNortonCodeTwentyShortUPhase p.1 p.2) •
        monsterNortonPureShort (monsterNortonCodeTwentyForwardShortIndex
          (monsterNortonCodeTwentyShortUOutput p))) =
      qSign (monsterNortonCodeTwentyShortUPhase p.1 p.2) •
        griessConwayEncode (monsterNortonPureShort (monsterNortonCodeTwentyForwardShortIndex
          (monsterNortonCodeTwentyShortUOutput p))) from griessConwayEncodeLinear.map_smul _ _]
  rw [monsterNortonPureShort, griessConwayEncode_decode _ (by intros; rfl)]
  simp only [Prod.smul_mk, smul_zero]

/-- The entire inverse short packet maps to the entire forward packet, with all phases retained. -/
theorem monsterNortonCodeTwentyShort_inverse :
    (y555NortonActualU⁻¹).val monsterNortonCodeTwentyInverseShort =
      monsterNortonCodeTwentyForwardShort := by
  rw [monsterNortonCodeTwentyInverseShort, map_sum]
  have ht (p : Fin 8 × Fin 32) :
      (y555NortonActualU⁻¹).val
        (((monsterNortonCodeTwentyInverseShortCoefficient p.1 p.2 : ℝ) / 32) •
          monsterNortonPureShort (monsterNortonCodeTwentyInverseShortIndex p)) =
        ((monsterNortonCodeTwentyForwardShortCoefficient
          (monsterNortonCodeTwentyShortUOutput p).1
          (monsterNortonCodeTwentyShortUOutput p).2 : ℝ) / 32) •
            monsterNortonPureShort (monsterNortonCodeTwentyForwardShortIndex
              (monsterNortonCodeTwentyShortUOutput p)) := by
    rw [map_smul, monsterNortonCodeTwentyShortU_unit, smul_smul]
    congr 1
    have h := congrArg (fun n : ℤ => (n : ℝ) / 32)
      (monsterNortonCodeTwentyShortU_coefficient p)
    simp only [Int.cast_mul, nortonUIntegerSign_real] at h
    linear_combination h
  simp_rw [ht]
  rw [monsterNortonCodeTwentyForwardShort]
  exact Fintype.sum_equiv
    (Equiv.ofBijective monsterNortonCodeTwentyShortUOutput
      monsterNortonCodeTwentyShortUOutput_bijective) _ _ (fun _ => rfl)

/-- The actual Norton operator sends the complete normalized forward short part to the inverse. -/
theorem monsterNortonCodeTwentyShort_forward :
    y555NortonActualU.val monsterNortonCodeTwentyForwardShort =
      monsterNortonCodeTwentyInverseShort := by
  have h := congrArg (fun x : GriessSpace => y555NortonActualU.val x)
    monsterNortonCodeTwentyShort_inverse
  change y555NortonActualU.val
    (y555NortonActualU.val.symm monsterNortonCodeTwentyInverseShort) =
      y555NortonActualU.val monsterNortonCodeTwentyForwardShort at h
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- Full actual spin and physical transport identifies the complete normalized tensor part. -/
theorem monsterNortonCodeTwentyTensor_forward :
    y555NortonActualU.val monsterNortonCodeTwentyForwardTensor =
      monsterNortonCodeTwentyInverseTensor := by
  rw [monsterNortonCodeTwentyForwardTensor, map_smul, ← monsterNortonULocal_generated]
  change (1 / (32 * Real.sqrt 2) : ℝ) • localGriessRepresentation monsterNortonUFiber
    (monsterNortonTensorLift (conwayTensorCoordinates
      (nortonUIntegerEmbed monsterNortonCodeTwentyForwardSpinInteger ⊗ₜ[ℝ]
        (fun j => (monsterNortonCodeTwentyForwardLeech j : ℝ))))) = _
  rw [monsterNortonLocal_tensor_product_actual, monsterNortonCodeTwentySpin_transport,
    monsterNortonCodeTwentyLeech_transport]
  rfl

/-- The literal seven-factor original Norton word sends the whole forward candidate to inverse. -/
theorem monsterNortonCodeTwentyU_transport :
    y555NortonActualU.val monsterNortonCodeTwentyForwardPacket =
      monsterNortonCodeTwentyInversePacket := by
  rw [monsterNortonCodeTwentyForwardPacket_parts, map_add, monsterNortonCodeTwentyShort_forward,
    monsterNortonCodeTwentyTensor_forward, ← monsterNortonCodeTwentyInversePacket_parts]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
