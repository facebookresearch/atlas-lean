/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual next V transport into a two-letter source XYZ vector. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01Thirteenth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQIntegerSparse

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem v_delta (d e : Fin 4096) (c : ℤ)
    (he : nortonUIntegerLabel (golayLabelCoefficients d + spinTranslation y555NortonVQ) = e)
    (hc : nortonUIntegerSign (spinPhase y555NortonVQ
      (golayLabelCoefficients d + spinTranslation y555NortonVQ)) = c) :
    nortonUIntegerQ y555NortonVQ (Pi.single d 1) = c • Pi.single e 1 := by
  rw [monsterNortonUIntegerQ_delta, he, hc]

private theorem q_add (q : Q) (a b : NortonUIntegerVector) :
    nortonUIntegerQ q (a + b) = nortonUIntegerQ q a + nortonUIntegerQ q b := by
  funext n
  simp only [nortonUIntegerQ, Pi.add_apply, mul_add]

private theorem v_two_deltas :
    nortonUIntegerQ y555NortonVQ monsterNortonLine01ThirteenthSpinVector =
      monsterNortonSourceYInteger 1038 := by
  have he0 : nortonUIntegerLabel
      (golayLabelCoefficients 0 + spinTranslation y555NortonVQ) = 1038 := by decide +kernel
  have hc0 : nortonUIntegerSign (spinPhase y555NortonVQ
      (golayLabelCoefficients 0 + spinTranslation y555NortonVQ)) = 1 := by decide +kernel
  have he1 : nortonUIntegerLabel
      (golayLabelCoefficients 2048 + spinTranslation y555NortonVQ) = 3086 := by decide +kernel
  have hc1 : nortonUIntegerSign (spinPhase y555NortonVQ
      (golayLabelCoefficients 2048 + spinTranslation y555NortonVQ)) = -1 := by decide +kernel
  rw [monsterNortonLine01ThirteenthSpinVector, q_add, v_delta 0 1038 1 he0 hc0,
    v_delta 2048 3086 (-1) he1 hc1, one_smul, neg_one_smul]
  rfl

private theorem source_y_spin :
    trialityYSpin (1038 : Fin 2048) (0 : Fin 24) =
      (1 / Real.sqrt 2 : ℝ) • nortonUIntegerEmbed (monsterNortonSourceYInteger 1038) := by
  have hc : (golayEncodedMask (1038 : Fin 2048).val).testBit (0 : Fin 24).val = false := by
    decide +kernel
  rw [monsterNortonSourceYSpin_basis, hc]
  have he : nortonUIntegerEmbed (monsterNortonSourceYInteger 1038) =
      (Pi.single (golayLabelCoefficients (1038 : Fin 4096)) 1 : SpinSpace) -
        Pi.single (golayLabelCoefficients (3086 : Fin 4096)) 1 := by
    have hi : nortonUIntegerEmbed (monsterNortonSourceYInteger 1038) =
        nortonUIntegerEmbed (Pi.single 1038 1) - nortonUIntegerEmbed (Pi.single 3086 1) := by
      ext t
      simp [monsterNortonSourceYInteger, nortonUIntegerEmbed]
    rw [hi, monsterNortonUIntegerEmbed_single, monsterNortonUIntegerEmbed_single]
  rw [he]
  rfl

private theorem column_rank_one (a : SpinSpace) (j : Fin 24) :
    monsterNortonTensorLift (conwaySpinColumn a j) =
      monsterNortonTensorRankOne (Pi.single j 1) a := by
  change monsterNortonTensorLift _ = monsterNortonTensorLift _
  congr 1
  ext t i
  simp only [conwaySpinColumn, conwayTensorCoordinates_tmul, Pi.single_apply]
  by_cases h : i = j <;> simp [h]

private theorem source_y_rank_one :
    trialityXYZBasis 1 (finProdFinEquiv ((1038 : Fin 2048), (0 : Fin 24))) =
      (1 / Real.sqrt 2 : ℝ) • monsterNortonTensorRankOne (Pi.single 0 1)
        (nortonUIntegerEmbed (monsterNortonSourceYInteger 1038)) := by
  rw [monsterNortonSourceY_tensor_column, column_rank_one, source_y_spin, map_smul]

private theorem v_x1038 :
    y555NortonV.val
      (trialityXYZBasis 0 (finProdFinEquiv ((1038 : Fin 2048), (0 : Fin 24)))) =
        trialityXYZBasis 0 (finProdFinEquiv ((1038 : Fin 2048), (0 : Fin 24))) := by
  have hp : monsterNortonSourceXQPhase y555NortonVQ 1038 0 = 0 := by decide +kernel
  rw [y555NortonV, monsterNortonQ_source_X, hp, qSign_zero, one_smul]

/-- The complete fourteenth vector consists of half the difference of source X1038 and Y1038. -/
noncomputable def monsterNortonLine01FourteenthVector : GriessSpace :=
  (1 / 2 : ℝ) • trialityXYZBasis 0 (finProdFinEquiv ((1038 : Fin 2048), (0 : Fin 24))) -
    (1 / 2 : ℝ) • trialityXYZBasis 1 (finProdFinEquiv ((1038 : Fin 2048), (0 : Fin 24)))

/-- Actual Norton V sends the entire thirteenth state to the displayed source XYZ difference. -/
theorem monsterNortonLine01Fourteenth_actual :
    y555NortonV.val monsterNortonLine01ThirteenthVector =
      monsterNortonLine01FourteenthVector := by
  rw [monsterNortonLine01ThirteenthVector, map_add, map_smul, v_x1038, map_smul]
  have ht : y555NortonV.val
      (monsterNortonTensorRankOne (Pi.single 0 1)
        (nortonUIntegerEmbed monsterNortonLine01ThirteenthSpinVector)) =
      monsterNortonTensorRankOne (Pi.single 0 1)
        (nortonUIntegerEmbed (monsterNortonSourceYInteger 1038)) := by
    change (qIntoGenerated y555NortonVQ).val
      (monsterNortonTensorLift (conwayTensorCoordinates _)) = _
    rw [monsterNortonQ_integer_rank_one, v_two_deltas]
    rfl
  rw [ht, monsterNortonLine01FourteenthVector, source_y_rank_one, smul_smul]
  have hc : (-1 / (2 * Real.sqrt 2) : ℝ) = -(1 / 2 * (1 / Real.sqrt 2)) := by ring
  rw [hc, neg_smul, sub_eq_add_neg]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
