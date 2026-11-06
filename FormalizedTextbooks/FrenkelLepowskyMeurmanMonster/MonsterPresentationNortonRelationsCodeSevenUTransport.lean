/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeSevenUPackets

/-! The actual Norton operator transports the whole original code-seven mixed candidate. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Every original inverse short unit has its complete signed inverse-U forward image. -/
theorem monsterNortonCodeSevenShortU_unit (p : Fin 8 × Fin 32) :
    (y555NortonActualU⁻¹).val
      (monsterNortonPureShort (monsterNortonCodeSevenInverseShortIndex p)) =
        qSign (monsterNortonCodeSevenShortUPhase p.1 p.2) •
          monsterNortonPureShort (monsterNortonCodeSevenForwardShortIndex
            (monsterNortonCodeSevenShortUOutput p)) := by
  rw [monsterNortonPureShort, monsterNortonCodeSevenShortU_actual]
  apply (Function.LeftInverse.injective griessConwayDecode_encode)
  rw [griessConwayEncode_decode _ (by intros; rfl)]
  rw [show griessConwayEncode
      (qSign (monsterNortonCodeSevenShortUPhase p.1 p.2) •
        monsterNortonPureShort (monsterNortonCodeSevenForwardShortIndex
          (monsterNortonCodeSevenShortUOutput p))) =
      qSign (monsterNortonCodeSevenShortUPhase p.1 p.2) •
        griessConwayEncode (monsterNortonPureShort (monsterNortonCodeSevenForwardShortIndex
          (monsterNortonCodeSevenShortUOutput p))) from griessConwayEncodeLinear.map_smul _ _]
  rw [monsterNortonPureShort, griessConwayEncode_decode _ (by intros; rfl)]
  simp only [Prod.smul_mk, smul_zero]

/-- The entire inverse short packet maps to the entire forward packet, with all phases retained. -/
theorem monsterNortonCodeSevenShort_inverse :
    (y555NortonActualU⁻¹).val monsterNortonCodeSevenInverseShort =
      monsterNortonCodeSevenForwardShort := by
  rw [monsterNortonCodeSevenInverseShort, map_sum]
  have ht (p : Fin 8 × Fin 32) :
      (y555NortonActualU⁻¹).val
        (((monsterNortonCodeSevenInverseShortCoefficient p.1 p.2 : ℝ) / 32) •
          monsterNortonPureShort (monsterNortonCodeSevenInverseShortIndex p)) =
        ((monsterNortonCodeSevenForwardShortCoefficient
          (monsterNortonCodeSevenShortUOutput p).1
          (monsterNortonCodeSevenShortUOutput p).2 : ℝ) / 32) •
            monsterNortonPureShort (monsterNortonCodeSevenForwardShortIndex
              (monsterNortonCodeSevenShortUOutput p)) := by
    rw [map_smul, monsterNortonCodeSevenShortU_unit, smul_smul]
    congr 1
    have h := congrArg (fun n : ℤ => (n : ℝ) / 32)
      (monsterNortonCodeSevenShortU_coefficient p)
    simp only [Int.cast_mul, nortonUIntegerSign_real] at h
    linear_combination h
  simp_rw [ht]
  rw [monsterNortonCodeSevenForwardShort]
  exact Fintype.sum_equiv
    (Equiv.ofBijective monsterNortonCodeSevenShortUOutput
      monsterNortonCodeSevenShortUOutput_bijective) _ _ (fun _ => rfl)

/-- The actual Norton operator sends the complete normalized forward short part to the inverse. -/
theorem monsterNortonCodeSevenShort_forward :
    y555NortonActualU.val monsterNortonCodeSevenForwardShort =
      monsterNortonCodeSevenInverseShort := by
  have h := congrArg (fun x : GriessSpace => y555NortonActualU.val x)
    monsterNortonCodeSevenShort_inverse
  change y555NortonActualU.val
    (y555NortonActualU.val.symm monsterNortonCodeSevenInverseShort) =
      y555NortonActualU.val monsterNortonCodeSevenForwardShort at h
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- Full actual spin and physical transport identifies the complete normalized tensor part. -/
theorem monsterNortonCodeSevenTensor_forward :
    y555NortonActualU.val monsterNortonCodeSevenForwardTensor =
      monsterNortonCodeSevenInverseTensor := by
  rw [monsterNortonCodeSevenForwardTensor, map_smul, ← monsterNortonULocal_generated]
  change (1 / (32 * Real.sqrt 2) : ℝ) • localGriessRepresentation monsterNortonUFiber
    (monsterNortonTensorLift (conwayTensorCoordinates
      (nortonUIntegerEmbed monsterNortonCodeSevenForwardSpinInteger ⊗ₜ[ℝ]
        (fun j => (monsterNortonCodeSevenForwardLeech j : ℝ))))) = _
  rw [monsterNortonLocal_tensor_product_actual, monsterNortonCodeSevenSpin_transport,
    monsterNortonCodeSevenLeech_transport]
  rfl

/-- The literal seven-factor original Norton word sends the whole forward candidate to inverse. -/
theorem monsterNortonCodeSevenU_transport :
    y555NortonActualU.val monsterNortonCodeSevenForwardPacket =
      monsterNortonCodeSevenInversePacket := by
  rw [monsterNortonCodeSevenForwardPacket_parts, map_add, monsterNortonCodeSevenShort_forward,
    monsterNortonCodeSevenTensor_forward, ← monsterNortonCodeSevenInversePacket_parts]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
