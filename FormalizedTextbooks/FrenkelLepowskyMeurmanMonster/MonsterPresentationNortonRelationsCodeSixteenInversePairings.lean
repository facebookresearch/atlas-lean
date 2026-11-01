/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual whole inverse-sixth packet reads on the normalized code-sixteen support. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeSixteenInverseCoefficients
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeSixteenInverseCoefficientActual
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortExtraTensorPairings

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem displayCodes_injective : Function.Injective monsterNortonRemainingOctadUCodes := by
  apply StrictMono.injective
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 75, monsterNortonRemainingOctadUCodes i.castSucc <
      monsterNortonRemainingOctadUCodes i.succ := by decide +kernel
  exact hc

private theorem short_form (e : Fin 64) (p : Fin 8 × Fin 32) :
    griessForm (monsterNortonShortExtraPacket (monsterNortonRemainingOctadUOutput 3 e))
      (monsterNortonPureShort (monsterNortonCodeSixteenInverseShortIndex p)) =
      if monsterNortonRemainingOctadUOutputIsOctad 3 e = true ∧
        monsterNortonRemainingOctadUOutputChoice 3 e =
          monsterNortonCodeSixteenInverseOctadChoice p.1 then
        (monsterNortonOctadPositiveInteger (monsterNortonCodeSixteenInverseSign p.1 p.2)
          (monsterNortonRemainingOctadUOutputSign 3 e) : ℝ) / 8
      else 0 := by
  unfold monsterNortonRemainingOctadUOutput monsterNortonCodeSixteenInverseShortIndex
  by_cases h : monsterNortonRemainingOctadUOutputIsOctad 3 e = true
  · simp only [h, ite_true, true_and]
    unfold monsterNortonRemainingOctadUOctad
    rw [monsterNortonOctadExtra_octad_form]
    simp only [displayCodes_injective.eq_iff]
  · simp only [h]
    exact monsterNortonOddExtra_short_form _ _ _

/-- Every whole inverse-sixth short pairing is its exact certified source coefficient. -/
theorem monsterNortonCodeSixteenInverseHalf_short_form (p : Fin 8 × Fin 32) :
    griessForm (monsterNortonRemainingOctadInverseSixthPacket 3)
      (monsterNortonPureShort (monsterNortonCodeSixteenInverseShortIndex p)) =
        (monsterNortonCodeSixteenInverseShortCoefficient p.1 p.2 : ℝ) / 32 := by
  rw [monsterNortonCodeSixteenInverseActualPacket_actual]
  unfold monsterNortonCodeSixteenInverseActualPacket
  rw [map_sum]
  simp only [LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, short_form]
  have he (e : Fin 64) :
      (monsterNortonCodeSixteenInverseCoefficientCache e : ℝ) / 8 *
        (if monsterNortonRemainingOctadUOutputIsOctad 3 e = true ∧
          monsterNortonRemainingOctadUOutputChoice 3 e =
            monsterNortonCodeSixteenInverseOctadChoice p.1 then
          (monsterNortonOctadPositiveInteger (monsterNortonCodeSixteenInverseSign p.1 p.2)
            (monsterNortonRemainingOctadUOutputSign 3 e) : ℝ) / 8 else 0) =
        ((if monsterNortonRemainingOctadUOutputIsOctad 3 e = true ∧
          monsterNortonRemainingOctadUOutputChoice 3 e =
            monsterNortonCodeSixteenInverseOctadChoice p.1 then
          monsterNortonCodeSixteenInverseCoefficientCache e *
            monsterNortonOctadPositiveInteger (monsterNortonCodeSixteenInverseSign p.1 p.2)
              (monsterNortonRemainingOctadUOutputSign 3 e) else 0 : ℤ) : ℝ) / 64 := by
    split_ifs <;> push_cast <;> ring
  simp_rw [he]
  rw [← Finset.sum_div, ← Int.cast_sum]
  change (monsterNortonCodeSixteenInverseShortRead p : ℝ) / 64 = _
  rw [monsterNortonCodeSixteenInverseShortRead_coefficient]
  push_cast
  ring

private theorem sign_last (i : Fin 16) :
    qSign (golayLabelCoefficients (monsterNortonCodeSixteenInverseSpinLabel i) 11) =
      if (monsterNortonCodeSixteenInverseSpinLabel i).val < 2048 then (1 : ℝ) else -1 := by
  have h : ∀ i : Fin 16,
      golayLabelCoefficients (monsterNortonCodeSixteenInverseSpinLabel i) 11 =
        (if (monsterNortonCodeSixteenInverseSpinLabel i).val < 2048 then 0 else 1 : ZMod 2) := by
    decide +kernel
  rw [h]
  split_ifs <;> norm_num [qSign]

private theorem tensor_form (e : Fin 64) (p : Fin 16 × Fin 4) :
    griessForm (monsterNortonShortExtraPacket (monsterNortonRemainingOctadUOutput 3 e))
      (monsterNortonTensorUnit (monsterNortonCodeSixteenInverseTensorIndex p).1
        (monsterNortonCodeSixteenInverseTensorIndex p).2) =
      if monsterNortonRemainingOctadUOutputIsOctad 3 e ≠ true ∧
        (monsterNortonRemainingOctadUOutputOddCode 3 e).val =
          (monsterNortonCodeSixteenInverseSpinLabel p.1).val % 2048 ∧
        monsterNortonRemainingOctadUOutputOddPosition 3 e =
          monsterNortonCodeSixteenInverseColumns p.2 then
        ((if (monsterNortonCodeSixteenInverseSpinLabel p.1).val < 2048 then (1 : ℤ) else -1) *
          (if (golayEncodedMask (monsterNortonRemainingOctadUOutputOddCode 3 e).val).testBit
            (monsterNortonCodeSixteenInverseColumns p.2).val then -1 else 1) : ℝ) / Real.sqrt 2
      else 0 := by
  unfold monsterNortonRemainingOctadUOutput monsterNortonCodeSixteenInverseTensorIndex
  by_cases h : monsterNortonRemainingOctadUOutputIsOctad 3 e = true
  · simp only [h, ite_true, ne_eq, not_true_eq_false, false_and, ite_false]
    exact monsterNortonOctadExtra_tensor_form _ _ _ _
  · simp only [h, Bool.false_eq_true, ite_false, ne_eq, not_false_eq_true, true_and]
    rw [monsterNortonOddExtra_tensor_form, sign_last]
    have hd : spinDictionaryCode
        (golayLabelCoefficients (monsterNortonCodeSixteenInverseSpinLabel p.1)) =
          monsterNortonRemainingOctadUOutputOddCode 3 e ↔
        (monsterNortonRemainingOctadUOutputOddCode 3 e).val =
          (monsterNortonCodeSixteenInverseSpinLabel p.1).val % 2048 := by
      simp only [spinDictionaryCode, spinDictionaryLabel_coeff, Fin.ext_iff]
      exact eq_comm
    simp only [hd]
    by_cases hp : monsterNortonCodeSixteenInverseColumns p.2 =
        monsterNortonRemainingOctadUOutputOddPosition 3 e
    · simp only [hp, true_and, and_true, Int.cast_ite, Int.cast_one, Int.cast_neg]
    · simp [hp, Ne.symm hp]

/-- Every whole inverse-sixth tensor pairing is its exact certified source coefficient. -/
theorem monsterNortonCodeSixteenInverseHalf_tensor_form (p : Fin 16 × Fin 4) :
    griessForm (monsterNortonRemainingOctadInverseSixthPacket 3)
      (monsterNortonTensorUnit (monsterNortonCodeSixteenInverseTensorIndex p).1
        (monsterNortonCodeSixteenInverseTensorIndex p).2) =
        (monsterNortonCodeSixteenInverseTensorCoefficient p : ℝ) / (32 * Real.sqrt 2) := by
  rw [monsterNortonCodeSixteenInverseActualPacket_actual]
  unfold monsterNortonCodeSixteenInverseActualPacket
  rw [map_sum]
  simp only [LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, tensor_form]
  have he (e : Fin 64) :
      (monsterNortonCodeSixteenInverseCoefficientCache e : ℝ) / 8 *
        (if monsterNortonRemainingOctadUOutputIsOctad 3 e ≠ true ∧
          (monsterNortonRemainingOctadUOutputOddCode 3 e).val =
            (monsterNortonCodeSixteenInverseSpinLabel p.1).val % 2048 ∧
          monsterNortonRemainingOctadUOutputOddPosition 3 e =
            monsterNortonCodeSixteenInverseColumns p.2 then
          ((if (monsterNortonCodeSixteenInverseSpinLabel p.1).val < 2048 then (1 : ℤ) else -1) *
            (if (golayEncodedMask (monsterNortonRemainingOctadUOutputOddCode 3 e).val).testBit
              (monsterNortonCodeSixteenInverseColumns p.2).val then -1 else 1) : ℝ) /
                Real.sqrt 2 else 0) =
        ((if monsterNortonRemainingOctadUOutputIsOctad 3 e ≠ true ∧
          (monsterNortonRemainingOctadUOutputOddCode 3 e).val =
            (monsterNortonCodeSixteenInverseSpinLabel p.1).val % 2048 ∧
          monsterNortonRemainingOctadUOutputOddPosition 3 e =
            monsterNortonCodeSixteenInverseColumns p.2 then
          monsterNortonCodeSixteenInverseCoefficientCache e *
            (if (monsterNortonCodeSixteenInverseSpinLabel p.1).val < 2048 then 1 else -1) *
            (if (golayEncodedMask (monsterNortonRemainingOctadUOutputOddCode 3 e).val).testBit
              (monsterNortonCodeSixteenInverseColumns p.2).val then -1 else 1) else 0 : ℤ) : ℝ) /
                (8 * Real.sqrt 2) := by
    split_ifs <;> push_cast <;> ring
  simp_rw [he]
  rw [← Finset.sum_div, ← Int.cast_sum]
  change (monsterNortonCodeSixteenInverseTensorRead p : ℝ) / (8 * Real.sqrt 2) = _
  have hr : 4 * (monsterNortonCodeSixteenInverseTensorRead p : ℝ) =
      (monsterNortonCodeSixteenInverseTensorCoefficient p : ℝ) := by
    exact_mod_cast monsterNortonCodeSixteenInverseTensorRead_coefficient p
  rw [← hr]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
