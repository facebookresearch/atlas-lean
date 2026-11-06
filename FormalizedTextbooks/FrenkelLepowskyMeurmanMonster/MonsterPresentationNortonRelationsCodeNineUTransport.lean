/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeNineUPackets

/-! The actual Norton operator transports the whole original code-nine mixed candidate. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Every original inverse short unit has its complete signed inverse-U forward image. -/
theorem monsterNortonCodeNineShortU_unit (p : Fin 8 × Fin 32) :
    (y555NortonActualU⁻¹).val
      (monsterNortonPureShort (monsterNortonCodeNineInverseShortIndex p)) =
        qSign (monsterNortonCodeNineShortUPhase p.1 p.2) •
          monsterNortonPureShort (monsterNortonCodeNineForwardShortIndex
            (monsterNortonCodeNineShortUOutput p)) := by
  rw [monsterNortonPureShort, monsterNortonCodeNineShortU_actual]
  apply (Function.LeftInverse.injective griessConwayDecode_encode)
  rw [griessConwayEncode_decode _ (by intros; rfl)]
  rw [show griessConwayEncode
      (qSign (monsterNortonCodeNineShortUPhase p.1 p.2) •
        monsterNortonPureShort (monsterNortonCodeNineForwardShortIndex
          (monsterNortonCodeNineShortUOutput p))) =
      qSign (monsterNortonCodeNineShortUPhase p.1 p.2) •
        griessConwayEncode (monsterNortonPureShort (monsterNortonCodeNineForwardShortIndex
          (monsterNortonCodeNineShortUOutput p))) from griessConwayEncodeLinear.map_smul _ _]
  rw [monsterNortonPureShort, griessConwayEncode_decode _ (by intros; rfl)]
  simp only [Prod.smul_mk, smul_zero]

/-- The entire inverse short packet maps to the entire forward packet, with all phases retained. -/
theorem monsterNortonCodeNineShort_inverse :
    (y555NortonActualU⁻¹).val monsterNortonCodeNineInverseShort =
      monsterNortonCodeNineForwardShort := by
  rw [monsterNortonCodeNineInverseShort, map_sum]
  have ht (p : Fin 8 × Fin 32) :
      (y555NortonActualU⁻¹).val
        (((monsterNortonCodeNineInverseShortCoefficient p.1 p.2 : ℝ) / 32) •
          monsterNortonPureShort (monsterNortonCodeNineInverseShortIndex p)) =
        ((monsterNortonCodeNineForwardShortCoefficient
          (monsterNortonCodeNineShortUOutput p).1
          (monsterNortonCodeNineShortUOutput p).2 : ℝ) / 32) •
            monsterNortonPureShort (monsterNortonCodeNineForwardShortIndex
              (monsterNortonCodeNineShortUOutput p)) := by
    rw [map_smul, monsterNortonCodeNineShortU_unit, smul_smul]
    congr 1
    have h := congrArg (fun n : ℤ => (n : ℝ) / 32)
      (monsterNortonCodeNineShortU_coefficient p)
    simp only [Int.cast_mul, nortonUIntegerSign_real] at h
    linear_combination h
  simp_rw [ht]
  rw [monsterNortonCodeNineForwardShort]
  exact Fintype.sum_equiv
    (Equiv.ofBijective monsterNortonCodeNineShortUOutput
      monsterNortonCodeNineShortUOutput_bijective) _ _ (fun _ => rfl)

/-- The actual Norton operator sends the complete normalized forward short part to the inverse. -/
theorem monsterNortonCodeNineShort_forward :
    y555NortonActualU.val monsterNortonCodeNineForwardShort =
      monsterNortonCodeNineInverseShort := by
  have h := congrArg (fun x : GriessSpace => y555NortonActualU.val x)
    monsterNortonCodeNineShort_inverse
  change y555NortonActualU.val
    (y555NortonActualU.val.symm monsterNortonCodeNineInverseShort) =
      y555NortonActualU.val monsterNortonCodeNineForwardShort at h
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- Full actual spin and physical transport identifies the complete normalized tensor part. -/
theorem monsterNortonCodeNineTensor_forward :
    y555NortonActualU.val monsterNortonCodeNineForwardTensor =
      monsterNortonCodeNineInverseTensor := by
  rw [monsterNortonCodeNineForwardTensor, map_smul, ← monsterNortonULocal_generated]
  change (1 / (32 * Real.sqrt 2) : ℝ) • localGriessRepresentation monsterNortonUFiber
    (monsterNortonTensorLift (conwayTensorCoordinates
      (nortonUIntegerEmbed monsterNortonCodeNineForwardSpinInteger ⊗ₜ[ℝ]
        (fun j => (monsterNortonCodeNineForwardLeech j : ℝ))))) = _
  rw [monsterNortonLocal_tensor_product_actual, monsterNortonCodeNineSpin_transport,
    monsterNortonCodeNineLeech_transport]
  rfl

/-- The literal seven-factor original Norton word sends the whole forward candidate to inverse. -/
theorem monsterNortonCodeNineU_transport :
    y555NortonActualU.val monsterNortonCodeNineForwardPacket =
      monsterNortonCodeNineInversePacket := by
  rw [monsterNortonCodeNineForwardPacket_parts, map_add, monsterNortonCodeNineShort_forward,
    monsterNortonCodeNineTensor_forward, ← monsterNortonCodeNineInversePacket_parts]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
