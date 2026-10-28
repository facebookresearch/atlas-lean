/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual whole inverse-sixth packet reads on the normalized code-twenty-two support. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyTwoInverseCoefficients
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyTwoInverseCoefficientActual
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

private theorem short_form (e : Fin 64) (p : Fin 16 × Fin 32) :
    griessForm (monsterNortonShortExtraPacket (monsterNortonRemainingOctadUOutput 9 e))
      (monsterNortonPureShort (monsterNortonCodeTwentyTwoInverseShortIndex p)) =
      if monsterNortonRemainingOctadUOutputIsOctad 9 e = true ∧
        monsterNortonRemainingOctadUOutputChoice 9 e =
          monsterNortonCodeTwentyTwoInverseOctadChoice p.1 then
        (monsterNortonOctadPositiveInteger (monsterNortonCodeTwentyTwoInverseSign p.1 p.2)
          (monsterNortonRemainingOctadUOutputSign 9 e) : ℝ) / 8
      else 0 := by
  unfold monsterNortonRemainingOctadUOutput monsterNortonCodeTwentyTwoInverseShortIndex
  by_cases h : monsterNortonRemainingOctadUOutputIsOctad 9 e = true
  · simp only [h, ite_true, true_and]
    unfold monsterNortonRemainingOctadUOctad
    rw [monsterNortonOctadExtra_octad_form]
    simp only [displayCodes_injective.eq_iff]
  · simp only [h]
    exact monsterNortonOddExtra_short_form _ _ _

/-- Every whole inverse-sixth short pairing is its exact certified source coefficient. -/
theorem monsterNortonCodeTwentyTwoInverseHalf_short_form (p : Fin 16 × Fin 32) :
    griessForm (monsterNortonRemainingOctadInverseSixthPacket 9)
      (monsterNortonPureShort (monsterNortonCodeTwentyTwoInverseShortIndex p)) =
        (monsterNortonCodeTwentyTwoInverseShortCoefficient p.1 p.2 : ℝ) / 32 := by
  rw [monsterNortonCodeTwentyTwoInverseActualPacket_actual]
  unfold monsterNortonCodeTwentyTwoInverseActualPacket
  rw [map_sum]
  simp only [LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, short_form]
  have he (e : Fin 64) :
      (monsterNortonCodeTwentyTwoInverseCoefficientCache e : ℝ) / 8 *
        (if monsterNortonRemainingOctadUOutputIsOctad 9 e = true ∧
          monsterNortonRemainingOctadUOutputChoice 9 e =
            monsterNortonCodeTwentyTwoInverseOctadChoice p.1 then
          (monsterNortonOctadPositiveInteger (monsterNortonCodeTwentyTwoInverseSign p.1 p.2)
            (monsterNortonRemainingOctadUOutputSign 9 e) : ℝ) / 8 else 0) =
        ((if monsterNortonRemainingOctadUOutputIsOctad 9 e = true ∧
          monsterNortonRemainingOctadUOutputChoice 9 e =
            monsterNortonCodeTwentyTwoInverseOctadChoice p.1 then
          monsterNortonCodeTwentyTwoInverseCoefficientCache e *
            monsterNortonOctadPositiveInteger (monsterNortonCodeTwentyTwoInverseSign p.1 p.2)
              (monsterNortonRemainingOctadUOutputSign 9 e) else 0 : ℤ) : ℝ) / 64 := by
    split_ifs <;> push_cast <;> ring
  simp_rw [he]
  rw [← Finset.sum_div, ← Int.cast_sum]
  change (monsterNortonCodeTwentyTwoInverseShortRead p : ℝ) / 64 = _
  rw [monsterNortonCodeTwentyTwoInverseShortRead_coefficient]
  push_cast
  ring

private theorem sign_last (i : Fin 16 × Fin 4) :
    qSign (golayLabelCoefficients (monsterNortonCodeTwentyTwoInverseSpinLabel i.1 i.2) 11) =
      if (monsterNortonCodeTwentyTwoInverseSpinLabel i.1 i.2).val < 2048 then (1 : ℝ) else -1 := by
  have h : ∀ i : Fin 16 × Fin 4,
      golayLabelCoefficients (monsterNortonCodeTwentyTwoInverseSpinLabel i.1 i.2) 11 =
        (if (monsterNortonCodeTwentyTwoInverseSpinLabel i.1 i.2).val < 2048 then 0 else 1 : ZMod
          2) := by
    decide +kernel
  rw [h]
  split_ifs <;> norm_num [qSign]

private theorem tensor_form (e : Fin 64) (p : Fin 16 × Fin 4) :
    griessForm (monsterNortonShortExtraPacket (monsterNortonRemainingOctadUOutput 9 e))
      (monsterNortonTensorUnit (monsterNortonCodeTwentyTwoInverseTensorIndex p).1
        (monsterNortonCodeTwentyTwoInverseTensorIndex p).2) =
      if monsterNortonRemainingOctadUOutputIsOctad 9 e ≠ true ∧
        (monsterNortonRemainingOctadUOutputOddCode 9 e).val =
          (monsterNortonCodeTwentyTwoInverseSpinLabel p.1 p.2).val % 2048 ∧
        monsterNortonRemainingOctadUOutputOddPosition 9 e =
          monsterNortonCodeTwentyTwoInverseColumns p.1 then
        ((if (monsterNortonCodeTwentyTwoInverseSpinLabel p.1 p.2).val < 2048 then (1 : ℤ) else -1) *
          (if (golayEncodedMask (monsterNortonRemainingOctadUOutputOddCode 9 e).val).testBit
            (monsterNortonCodeTwentyTwoInverseColumns p.1).val then -1 else 1) : ℝ) / Real.sqrt 2
      else 0 := by
  unfold monsterNortonRemainingOctadUOutput monsterNortonCodeTwentyTwoInverseTensorIndex
  by_cases h : monsterNortonRemainingOctadUOutputIsOctad 9 e = true
  · simp only [h, ite_true, ne_eq, not_true_eq_false, false_and, ite_false]
    exact monsterNortonOctadExtra_tensor_form _ _ _ _
  · simp only [h, Bool.false_eq_true, ite_false, ne_eq, not_false_eq_true, true_and]
    rw [monsterNortonOddExtra_tensor_form, sign_last]
    have hd : spinDictionaryCode
        (golayLabelCoefficients (monsterNortonCodeTwentyTwoInverseSpinLabel p.1 p.2)) =
          monsterNortonRemainingOctadUOutputOddCode 9 e ↔
        (monsterNortonRemainingOctadUOutputOddCode 9 e).val =
          (monsterNortonCodeTwentyTwoInverseSpinLabel p.1 p.2).val % 2048 := by
      simp only [spinDictionaryCode, spinDictionaryLabel_coeff, Fin.ext_iff]
      exact eq_comm
    simp only [hd]
    by_cases hp : monsterNortonCodeTwentyTwoInverseColumns p.1 =
        monsterNortonRemainingOctadUOutputOddPosition 9 e
    · simp only [hp, true_and, and_true, Int.cast_ite, Int.cast_one, Int.cast_neg]
    · simp [hp, Ne.symm hp]

/-- Every whole inverse-sixth tensor pairing is its exact certified source coefficient. -/
theorem monsterNortonCodeTwentyTwoInverseHalf_tensor_form (p : Fin 16 × Fin 4) :
    griessForm (monsterNortonRemainingOctadInverseSixthPacket 9)
      (monsterNortonTensorUnit (monsterNortonCodeTwentyTwoInverseTensorIndex p).1
        (monsterNortonCodeTwentyTwoInverseTensorIndex p).2) =
        (monsterNortonCodeTwentyTwoInverseTensorCoefficient p : ℝ) / (32 * Real.sqrt 2) := by
  rw [monsterNortonCodeTwentyTwoInverseActualPacket_actual]
  unfold monsterNortonCodeTwentyTwoInverseActualPacket
  rw [map_sum]
  simp only [LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, tensor_form]
  have he (e : Fin 64) :
      (monsterNortonCodeTwentyTwoInverseCoefficientCache e : ℝ) / 8 *
        (if monsterNortonRemainingOctadUOutputIsOctad 9 e ≠ true ∧
          (monsterNortonRemainingOctadUOutputOddCode 9 e).val =
            (monsterNortonCodeTwentyTwoInverseSpinLabel p.1 p.2).val % 2048 ∧
          monsterNortonRemainingOctadUOutputOddPosition 9 e =
            monsterNortonCodeTwentyTwoInverseColumns p.1 then
          ((if (monsterNortonCodeTwentyTwoInverseSpinLabel p.1 p.2).val < 2048 then (1 : ℤ) else
            -1) *
            (if (golayEncodedMask (monsterNortonRemainingOctadUOutputOddCode 9 e).val).testBit
              (monsterNortonCodeTwentyTwoInverseColumns p.1).val then -1 else 1) : ℝ) /
                Real.sqrt 2 else 0) =
        ((if monsterNortonRemainingOctadUOutputIsOctad 9 e ≠ true ∧
          (monsterNortonRemainingOctadUOutputOddCode 9 e).val =
            (monsterNortonCodeTwentyTwoInverseSpinLabel p.1 p.2).val % 2048 ∧
          monsterNortonRemainingOctadUOutputOddPosition 9 e =
            monsterNortonCodeTwentyTwoInverseColumns p.1 then
          monsterNortonCodeTwentyTwoInverseCoefficientCache e *
            (if (monsterNortonCodeTwentyTwoInverseSpinLabel p.1 p.2).val < 2048 then 1 else -1) *
            (if (golayEncodedMask (monsterNortonRemainingOctadUOutputOddCode 9 e).val).testBit
              (monsterNortonCodeTwentyTwoInverseColumns p.1).val then -1 else 1) else 0 : ℤ) : ℝ) /
                (8 * Real.sqrt 2) := by
    split_ifs <;> push_cast <;> ring
  simp_rw [he]
  rw [← Finset.sum_div, ← Int.cast_sum]
  change (monsterNortonCodeTwentyTwoInverseTensorRead p : ℝ) / (8 * Real.sqrt 2) = _
  have hr : 4 * (monsterNortonCodeTwentyTwoInverseTensorRead p : ℝ) =
      (monsterNortonCodeTwentyTwoInverseTensorCoefficient p : ℝ) := by
    exact_mod_cast monsterNortonCodeTwentyTwoInverseTensorRead_coefficient p
  rw [← hr]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
