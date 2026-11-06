/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The first literal v,u tensor steps in the actual first Norton line-pair word. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01TensorInitialData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQTensorBasis

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped TensorProduct Matrix
set_option backward.isDefEq.respectTransparency false

/-- The actual nonzero tensor input, normalized to rational sparse word coordinates. -/
noncomputable def monsterNortonLine01TensorStart : GriessSpace :=
  (1 / 4 : ℝ) • monsterNortonIntegralTensorVector (Pi.single 0 1) (Pi.single 0 1)

/-- The actual integer rank-one tensor after the first literal Norton v. -/
noncomputable def monsterNortonLine01TensorAfterV : GriessSpace :=
  (1 / 4 : ℝ) • monsterNortonIntegralTensorVector (Pi.single 1038 1) (Pi.single 0 1)

/-- The complete signed integer rank-one tensor after the next literal Norton u. -/
noncomputable def monsterNortonLine01TensorAfterVU : GriessSpace :=
  (1 / 32 : ℝ) • monsterNortonIntegralTensorVector
    monsterNortonLine01InitialSpin monsterNortonLine01InitialLeech

/-- The actual rationally normalized input has a nonzero genuine tensor coordinate. -/
theorem monsterNortonLine01TensorStart_tensor_ne_zero :
    (griessConwayEncode monsterNortonLine01TensorStart).2.2 ≠ 0 := by
  change (griessConwayEncode ((1 / 4 : ℝ) •
    monsterNortonIntegralTensorVector (Pi.single 0 1) (Pi.single 0 1))).2.2 ≠ 0
  intro h
  have he := griessConwayEncodeLinear.map_smul (1 / 4 : ℝ)
    (monsterNortonIntegralTensorVector (Pi.single 0 1) (Pi.single 0 1))
  change griessConwayEncode ((1 / 4 : ℝ) •
    monsterNortonIntegralTensorVector (Pi.single 0 1) (Pi.single 0 1)) =
      (1 / 4 : ℝ) • griessConwayEncode
        (monsterNortonIntegralTensorVector (Pi.single 0 1) (Pi.single 0 1)) at he
  rw [monsterNortonIntegralTensorVector_encode] at he
  have hc := congrArg (fun a : ConwayRawSpace => a.2.2 (0 : SpinIndex) (0 : Fin 24)) he
  simp only [Prod.smul_mk, Pi.smul_apply, conwayTensorCoordinates_tmul, smul_eq_mul] at hc
  have hz := congrFun (congrFun h (0 : SpinIndex)) (0 : Fin 24)
  change (griessConwayEncode ((1 / 4 : ℝ) •
    monsterNortonIntegralTensorVector (Pi.single 0 1) (Pi.single 0 1))).2.2 0 0 = 0 at hz
  rw [hc] at hz
  have hl : nortonUIntegerLabel (0 : SpinIndex) = 0 := by decide +kernel
  have hb : (leechBasisMatrix *ᵥ (Pi.single 0 1 : Fin 24 → ℤ)) 0 = 8 := by decide +kernel
  simp only [nortonUIntegerEmbed, hl, Pi.single_eq_same, Int.cast_one, one_mul,
    leechCoordinateEmbedding, LinearMap.coe_mk, AddHom.coe_mk, hb] at hz
  have hs : Real.sqrt 8 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  field_simp [hs] at hz
  norm_num at hz

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- The literal Q phase and translation are checked before transporting the actual spin delta.
/-- Literal Norton v translates the first integer delta without an unproved central phase. -/
theorem monsterNortonLine01TensorV_spin_certificate :
    nortonUIntegerQ y555NortonVQ (Pi.single 0 1) = Pi.single 1038 1 := by
  have hc : golayLabelCoefficients (0 : Fin 4096) = 0 := by decide +kernel
  have ht : spinTranslation y555NortonVQ = golayLabelCoefficients 1038 := by decide +kernel
  have hp : Multiplicative.toAdd y555NortonVQ.coeff +
      spinDot (spinModulation y555NortonVQ) (spinTranslation y555NortonVQ) = 0 := by
    decide +kernel
  have hs : spinRepresentation y555NortonVQ (Pi.single (golayLabelCoefficients 0) 1) =
      Pi.single (golayLabelCoefficients 1038) 1 := by
    change spinOperator y555NortonVQ (Pi.single (golayLabelCoefficients 0) 1) = _
    rw [hc, monsterNortonQ_spin_delta, zero_add, hp, qSign_zero, one_smul, ht]
  have hl := congrArg (fun v : SpinSpace => spinRepresentation y555NortonVQ v)
    (monsterNortonUIntegerEmbed_single 0)
  have he := (nortonUIntegerQ_embed y555NortonVQ (Pi.single 0 1)).symm.trans
    (hl.trans hs)
  have he' := he.trans (monsterNortonUIntegerEmbed_single 1038).symm
  funext n
  apply Int.cast_injective (α := ℝ)
  have hn := congrFun he' (golayLabelCoefficients n)
  simpa only [nortonUIntegerEmbed, nortonUIntegerLabel_coeff] using hn

/-- The first v step is an equality of entire actual Griess vectors. -/
theorem monsterNortonLine01TensorV_actual :
    y555NortonV.val monsterNortonLine01TensorStart = monsterNortonLine01TensorAfterV := by
  rw [monsterNortonLine01TensorStart, map_smul, monsterNortonVIntegralVector_actual,
    monsterNortonLine01TensorV_spin_certificate]
  rfl

private theorem integral_tensor_neg (v : NortonUIntegerVector) (z : Fin 24 → ℤ) :
    monsterNortonIntegralTensorVector (-v) z = -monsterNortonIntegralTensorVector v z := by
  have hv : nortonUIntegerEmbed (-v) = -nortonUIntegerEmbed v := by
    funext t
    simp only [nortonUIntegerEmbed, Pi.neg_apply, Int.cast_neg]
  change monsterNortonTensorLift (conwayTensorCoordinates
    (nortonUIntegerEmbed (-v) ⊗ₜ[ℝ]
      leechCoordinateEmbedding (leechBasisMatrix *ᵥ z))) =
        -monsterNortonTensorLift (conwayTensorCoordinates
          (nortonUIntegerEmbed v ⊗ₜ[ℝ] leechCoordinateEmbedding (leechBasisMatrix *ᵥ z)))
  rw [hv, TensorProduct.neg_tmul, map_neg, map_neg]

/-- The next u step is the proved full compact actual action, with both finite certificates. -/
theorem monsterNortonLine01TensorU_actual :
    y555NortonActualU.val monsterNortonLine01TensorAfterV =
      monsterNortonLine01TensorAfterVU := by
  rw [monsterNortonLine01TensorAfterV, map_smul, monsterNortonUCompactIntegralVector_forward,
    monsterNortonLine01InitialSpin_certificate, monsterNortonLine01InitialLeech_certificate,
    integral_tensor_neg, smul_neg, ← neg_smul, smul_smul, monsterNortonLine01TensorAfterVU]
  congr 1
  norm_num

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
