/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyTwoUPackets
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyTwoSpinGaussian
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyTwoShortUCertificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsTensorRowTransport

/-! The actual Norton operator transports the whole original code-twenty-two mixed candidate. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Every original inverse short unit has its complete signed inverse-U forward image. -/
theorem monsterNortonCodeTwentyTwoShortU_unit (p : Fin 16 × Fin 32) :
    (y555NortonActualU⁻¹).val
      (monsterNortonPureShort (monsterNortonCodeTwentyTwoInverseShortIndex p)) =
        qSign (monsterNortonCodeTwentyTwoShortUPhase p.1 p.2) •
          monsterNortonPureShort (monsterNortonCodeTwentyTwoForwardShortIndex
            (monsterNortonCodeTwentyTwoShortUOutput p)) := by
  rw [monsterNortonPureShort, monsterNortonCodeTwentyTwoShortU_actual]
  apply (Function.LeftInverse.injective griessConwayDecode_encode)
  rw [griessConwayEncode_decode _ (by intros; rfl)]
  rw [show griessConwayEncode
      (qSign (monsterNortonCodeTwentyTwoShortUPhase p.1 p.2) •
        monsterNortonPureShort (monsterNortonCodeTwentyTwoForwardShortIndex
          (monsterNortonCodeTwentyTwoShortUOutput p))) =
      qSign (monsterNortonCodeTwentyTwoShortUPhase p.1 p.2) •
        griessConwayEncode (monsterNortonPureShort (monsterNortonCodeTwentyTwoForwardShortIndex
          (monsterNortonCodeTwentyTwoShortUOutput p))) from griessConwayEncodeLinear.map_smul _ _]
  rw [monsterNortonPureShort, griessConwayEncode_decode _ (by intros; rfl)]
  simp only [Prod.smul_mk, smul_zero]

/-- The entire inverse short packet maps to the entire forward packet, with all phases retained. -/
theorem monsterNortonCodeTwentyTwoShort_inverse :
    (y555NortonActualU⁻¹).val monsterNortonCodeTwentyTwoInverseShort =
      monsterNortonCodeTwentyTwoForwardShort := by
  rw [monsterNortonCodeTwentyTwoInverseShort, map_sum]
  have ht (p : Fin 16 × Fin 32) :
      (y555NortonActualU⁻¹).val
        (((monsterNortonCodeTwentyTwoInverseShortCoefficient p.1 p.2 : ℝ) / 32) •
          monsterNortonPureShort (monsterNortonCodeTwentyTwoInverseShortIndex p)) =
        ((monsterNortonCodeTwentyTwoForwardShortCoefficient
          (monsterNortonCodeTwentyTwoShortUOutput p).1
          (monsterNortonCodeTwentyTwoShortUOutput p).2 : ℝ) / 32) •
            monsterNortonPureShort (monsterNortonCodeTwentyTwoForwardShortIndex
              (monsterNortonCodeTwentyTwoShortUOutput p)) := by
    rw [map_smul, monsterNortonCodeTwentyTwoShortU_unit, smul_smul]
    congr 1
    have h := congrArg (fun n : ℤ => (n : ℝ) / 32)
      (monsterNortonCodeTwentyTwoShortU_coefficient p)
    simp only [Int.cast_mul, nortonUIntegerSign_real] at h
    linear_combination h
  simp_rw [ht]
  rw [monsterNortonCodeTwentyTwoForwardShort]
  exact Fintype.sum_equiv
    (Equiv.ofBijective monsterNortonCodeTwentyTwoShortUOutput
      monsterNortonCodeTwentyTwoShortUOutput_bijective) _ _ (fun _ => rfl)

/-- The actual Norton operator sends the complete normalized forward short part to the inverse. -/
theorem monsterNortonCodeTwentyTwoShort_forward :
    y555NortonActualU.val monsterNortonCodeTwentyTwoForwardShort =
      monsterNortonCodeTwentyTwoInverseShort := by
  have h := congrArg (fun x : GriessSpace => y555NortonActualU.val x)
    monsterNortonCodeTwentyTwoShort_inverse
  change y555NortonActualU.val
    (y555NortonActualU.val.symm monsterNortonCodeTwentyTwoInverseShort) =
      y555NortonActualU.val monsterNortonCodeTwentyTwoForwardShort at h
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- Full actual row transport identifies every component of the normalized tensor part. -/
theorem monsterNortonCodeTwentyTwoTensor_forward :
    y555NortonActualU.val monsterNortonCodeTwentyTwoForwardTensor =
      monsterNortonCodeTwentyTwoInverseTensor := by
  rw [monsterNortonCodeTwentyTwoForwardTensor, map_smul, ← monsterNortonULocal_generated,
    monsterNortonCodeTwentyTwoInverseTensor]
  change (1 / (32 * Real.sqrt 2) : ℝ) • localGriessRepresentation monsterNortonUFiber
    (∑ s : Fin 64, monsterNortonTensorLift (conwayTensorCoordinates
      ((Pi.single (golayLabelCoefficients (monsterNortonCodeTwentyTwoForwardSpinLabel s)) 1 :
        SpinSpace) ⊗ₜ[ℝ] monsterNortonCodeTwentyTwoLeechRow s))) = _
  apply congrArg (fun x : GriessSpace => (1 / (32 * Real.sqrt 2) : ℝ) • x)
  apply monsterNortonLocal_tensor_rows_actual monsterNortonUFiber
    (fun s => Pi.single (golayLabelCoefficients (monsterNortonCodeTwentyTwoForwardSpinLabel s))
      1 : Fin 64 → SpinSpace)
    monsterNortonCodeTwentyTwoLeechRow monsterNortonCodeTwentyTwoInverseColumns
    (fun k s => (monsterNortonCodeTwentyTwoPreSpinColumnCoefficient k s : ℝ))
    (fun k => nortonUIntegerEmbed (monsterNortonCodeTwentyTwoInverseSpinInteger k))
  · exact monsterNortonCodeTwentyTwoLeechRow_transport
  · intro k
    have he : (∑ s : Fin 64, (monsterNortonCodeTwentyTwoPreSpinColumnCoefficient k s : ℝ) •
        (Pi.single (golayLabelCoefficients (monsterNortonCodeTwentyTwoForwardSpinLabel s)) 1 :
          SpinSpace)) =
        nortonUIntegerEmbed (monsterNortonCodeTwentyTwoForwardSpinInteger k) :=
      (monsterNortonUIntegerEmbed_packet
        (monsterNortonCodeTwentyTwoPreSpinColumnCoefficient k)
        monsterNortonCodeTwentyTwoForwardSpinLabel).symm
    rw [he]
    exact monsterNortonCodeTwentyTwoSpin_transport k

/-- The literal seven-factor original Norton word sends the whole forward candidate to inverse. -/
theorem monsterNortonCodeTwentyTwoU_transport :
    y555NortonActualU.val monsterNortonCodeTwentyTwoForwardPacket =
      monsterNortonCodeTwentyTwoInversePacket := by
  rw [monsterNortonCodeTwentyTwoForwardPacket_parts, map_add,
    monsterNortonCodeTwentyTwoShort_forward,
    monsterNortonCodeTwentyTwoTensor_forward, ← monsterNortonCodeTwentyTwoInversePacket_parts]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
