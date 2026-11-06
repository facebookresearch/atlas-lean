/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual whole inverse-sixth packet reads on the normalized code-twenty support. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyInverseCoefficients
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyInverseCoefficientActual
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
    griessForm (monsterNortonShortExtraPacket (monsterNortonRemainingOctadUOutput 7 e))
      (monsterNortonPureShort (monsterNortonCodeTwentyInverseShortIndex p)) =
      if monsterNortonRemainingOctadUOutputIsOctad 7 e = true ∧
        monsterNortonRemainingOctadUOutputChoice 7 e =
          monsterNortonCodeTwentyInverseOctadChoice p.1 then
        (monsterNortonOctadPositiveInteger (monsterNortonCodeTwentyInverseSign p.1 p.2)
          (monsterNortonRemainingOctadUOutputSign 7 e) : ℝ) / 8
      else 0 := by
  unfold monsterNortonRemainingOctadUOutput monsterNortonCodeTwentyInverseShortIndex
  by_cases h : monsterNortonRemainingOctadUOutputIsOctad 7 e = true
  · simp only [h, ite_true, true_and]
    unfold monsterNortonRemainingOctadUOctad
    rw [monsterNortonOctadExtra_octad_form]
    simp only [displayCodes_injective.eq_iff]
  · simp only [h]
    exact monsterNortonOddExtra_short_form _ _ _

/-- Every whole inverse-sixth short pairing is its exact certified source coefficient. -/
theorem monsterNortonCodeTwentyInverseHalf_short_form (p : Fin 8 × Fin 32) :
    griessForm (monsterNortonRemainingOctadInverseSixthPacket 7)
      (monsterNortonPureShort (monsterNortonCodeTwentyInverseShortIndex p)) =
        (monsterNortonCodeTwentyInverseShortCoefficient p.1 p.2 : ℝ) / 32 := by
  rw [monsterNortonCodeTwentyInverseActualPacket_actual]
  unfold monsterNortonCodeTwentyInverseActualPacket
  rw [map_sum]
  simp only [LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, short_form]
  have he (e : Fin 64) :
      (monsterNortonCodeTwentyInverseCoefficientCache e : ℝ) / 8 *
        (if monsterNortonRemainingOctadUOutputIsOctad 7 e = true ∧
          monsterNortonRemainingOctadUOutputChoice 7 e =
            monsterNortonCodeTwentyInverseOctadChoice p.1 then
          (monsterNortonOctadPositiveInteger (monsterNortonCodeTwentyInverseSign p.1 p.2)
            (monsterNortonRemainingOctadUOutputSign 7 e) : ℝ) / 8 else 0) =
        ((if monsterNortonRemainingOctadUOutputIsOctad 7 e = true ∧
          monsterNortonRemainingOctadUOutputChoice 7 e =
            monsterNortonCodeTwentyInverseOctadChoice p.1 then
          monsterNortonCodeTwentyInverseCoefficientCache e *
            monsterNortonOctadPositiveInteger (monsterNortonCodeTwentyInverseSign p.1 p.2)
              (monsterNortonRemainingOctadUOutputSign 7 e) else 0 : ℤ) : ℝ) / 64 := by
    split_ifs <;> push_cast <;> ring
  simp_rw [he]
  rw [← Finset.sum_div, ← Int.cast_sum]
  change (monsterNortonCodeTwentyInverseShortRead p : ℝ) / 64 = _
  rw [monsterNortonCodeTwentyInverseShortRead_coefficient]
  push_cast
  ring

private theorem sign_last (i : Fin 16) :
    qSign (golayLabelCoefficients (monsterNortonCodeTwentyInverseSpinLabel i) 11) =
      if (monsterNortonCodeTwentyInverseSpinLabel i).val < 2048 then (1 : ℝ) else -1 := by
  have h : ∀ i : Fin 16,
      golayLabelCoefficients (monsterNortonCodeTwentyInverseSpinLabel i) 11 =
        (if (monsterNortonCodeTwentyInverseSpinLabel i).val < 2048 then 0 else 1 : ZMod 2) := by
    decide +kernel
  rw [h]
  split_ifs <;> norm_num [qSign]

private theorem tensor_form (e : Fin 64) (p : Fin 16 × Fin 4) :
    griessForm (monsterNortonShortExtraPacket (monsterNortonRemainingOctadUOutput 7 e))
      (monsterNortonTensorUnit (monsterNortonCodeTwentyInverseTensorIndex p).1
        (monsterNortonCodeTwentyInverseTensorIndex p).2) =
      if monsterNortonRemainingOctadUOutputIsOctad 7 e ≠ true ∧
        (monsterNortonRemainingOctadUOutputOddCode 7 e).val =
          (monsterNortonCodeTwentyInverseSpinLabel p.1).val % 2048 ∧
        monsterNortonRemainingOctadUOutputOddPosition 7 e =
          monsterNortonCodeTwentyInverseColumns p.2 then
        ((if (monsterNortonCodeTwentyInverseSpinLabel p.1).val < 2048 then (1 : ℤ) else -1) *
          (if (golayEncodedMask (monsterNortonRemainingOctadUOutputOddCode 7 e).val).testBit
            (monsterNortonCodeTwentyInverseColumns p.2).val then -1 else 1) : ℝ) / Real.sqrt 2
      else 0 := by
  unfold monsterNortonRemainingOctadUOutput monsterNortonCodeTwentyInverseTensorIndex
  by_cases h : monsterNortonRemainingOctadUOutputIsOctad 7 e = true
  · simp only [h, ite_true, ne_eq, not_true_eq_false, false_and, ite_false]
    exact monsterNortonOctadExtra_tensor_form _ _ _ _
  · simp only [h, Bool.false_eq_true, ite_false, ne_eq, not_false_eq_true, true_and]
    rw [monsterNortonOddExtra_tensor_form, sign_last]
    have hd : spinDictionaryCode
        (golayLabelCoefficients (monsterNortonCodeTwentyInverseSpinLabel p.1)) =
          monsterNortonRemainingOctadUOutputOddCode 7 e ↔
        (monsterNortonRemainingOctadUOutputOddCode 7 e).val =
          (monsterNortonCodeTwentyInverseSpinLabel p.1).val % 2048 := by
      simp only [spinDictionaryCode, spinDictionaryLabel_coeff, Fin.ext_iff]
      exact eq_comm
    simp only [hd]
    by_cases hp : monsterNortonCodeTwentyInverseColumns p.2 =
        monsterNortonRemainingOctadUOutputOddPosition 7 e
    · simp only [hp, true_and, and_true, Int.cast_ite, Int.cast_one, Int.cast_neg]
    · simp [hp, Ne.symm hp]

/-- Every whole inverse-sixth tensor pairing is its exact certified source coefficient. -/
theorem monsterNortonCodeTwentyInverseHalf_tensor_form (p : Fin 16 × Fin 4) :
    griessForm (monsterNortonRemainingOctadInverseSixthPacket 7)
      (monsterNortonTensorUnit (monsterNortonCodeTwentyInverseTensorIndex p).1
        (monsterNortonCodeTwentyInverseTensorIndex p).2) =
        (monsterNortonCodeTwentyInverseTensorCoefficient p : ℝ) / (32 * Real.sqrt 2) := by
  rw [monsterNortonCodeTwentyInverseActualPacket_actual]
  unfold monsterNortonCodeTwentyInverseActualPacket
  rw [map_sum]
  simp only [LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, tensor_form]
  have he (e : Fin 64) :
      (monsterNortonCodeTwentyInverseCoefficientCache e : ℝ) / 8 *
        (if monsterNortonRemainingOctadUOutputIsOctad 7 e ≠ true ∧
          (monsterNortonRemainingOctadUOutputOddCode 7 e).val =
            (monsterNortonCodeTwentyInverseSpinLabel p.1).val % 2048 ∧
          monsterNortonRemainingOctadUOutputOddPosition 7 e =
            monsterNortonCodeTwentyInverseColumns p.2 then
          ((if (monsterNortonCodeTwentyInverseSpinLabel p.1).val < 2048 then (1 : ℤ) else -1) *
            (if (golayEncodedMask (monsterNortonRemainingOctadUOutputOddCode 7 e).val).testBit
              (monsterNortonCodeTwentyInverseColumns p.2).val then -1 else 1) : ℝ) /
                Real.sqrt 2 else 0) =
        ((if monsterNortonRemainingOctadUOutputIsOctad 7 e ≠ true ∧
          (monsterNortonRemainingOctadUOutputOddCode 7 e).val =
            (monsterNortonCodeTwentyInverseSpinLabel p.1).val % 2048 ∧
          monsterNortonRemainingOctadUOutputOddPosition 7 e =
            monsterNortonCodeTwentyInverseColumns p.2 then
          monsterNortonCodeTwentyInverseCoefficientCache e *
            (if (monsterNortonCodeTwentyInverseSpinLabel p.1).val < 2048 then 1 else -1) *
            (if (golayEncodedMask (monsterNortonRemainingOctadUOutputOddCode 7 e).val).testBit
              (monsterNortonCodeTwentyInverseColumns p.2).val then -1 else 1) else 0 : ℤ) : ℝ) /
                (8 * Real.sqrt 2) := by
    split_ifs <;> push_cast <;> ring
  simp_rw [he]
  rw [← Finset.sum_div, ← Int.cast_sum]
  change (monsterNortonCodeTwentyInverseTensorRead p : ℝ) / (8 * Real.sqrt 2) = _
  have hr : 4 * (monsterNortonCodeTwentyInverseTensorRead p : ℝ) =
      (monsterNortonCodeTwentyInverseTensorCoefficient p : ℝ) := by
    exact_mod_cast monsterNortonCodeTwentyInverseTensorRead_coefficient p
  rw [← hr]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
