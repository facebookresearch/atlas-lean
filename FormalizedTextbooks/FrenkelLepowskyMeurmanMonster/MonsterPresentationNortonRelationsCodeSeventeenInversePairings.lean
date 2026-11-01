/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual whole inverse-sixth packet reads on the normalized code-seventeen support. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeSeventeenInverseCoefficients
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeSeventeenInverseCoefficientActual
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
    griessForm (monsterNortonShortExtraPacket (monsterNortonRemainingOctadUOutput 4 e))
      (monsterNortonPureShort (monsterNortonCodeSeventeenInverseShortIndex p)) =
      if monsterNortonRemainingOctadUOutputIsOctad 4 e = true ∧
        monsterNortonRemainingOctadUOutputChoice 4 e =
          monsterNortonCodeSeventeenInverseOctadChoice p.1 then
        (monsterNortonOctadPositiveInteger (monsterNortonCodeSeventeenInverseSign p.1 p.2)
          (monsterNortonRemainingOctadUOutputSign 4 e) : ℝ) / 8
      else 0 := by
  unfold monsterNortonRemainingOctadUOutput monsterNortonCodeSeventeenInverseShortIndex
  by_cases h : monsterNortonRemainingOctadUOutputIsOctad 4 e = true
  · simp only [h, ite_true, true_and]
    unfold monsterNortonRemainingOctadUOctad
    rw [monsterNortonOctadExtra_octad_form]
    simp only [displayCodes_injective.eq_iff]
  · simp only [h]
    exact monsterNortonOddExtra_short_form _ _ _

/-- Every whole inverse-sixth short pairing is its exact certified source coefficient. -/
theorem monsterNortonCodeSeventeenInverseHalf_short_form (p : Fin 8 × Fin 32) :
    griessForm (monsterNortonRemainingOctadInverseSixthPacket 4)
      (monsterNortonPureShort (monsterNortonCodeSeventeenInverseShortIndex p)) =
        (monsterNortonCodeSeventeenInverseShortCoefficient p.1 p.2 : ℝ) / 32 := by
  rw [monsterNortonCodeSeventeenInverseActualPacket_actual]
  unfold monsterNortonCodeSeventeenInverseActualPacket
  rw [map_sum]
  simp only [LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, short_form]
  have he (e : Fin 64) :
      (monsterNortonCodeSeventeenInverseCoefficientCache e : ℝ) / 8 *
        (if monsterNortonRemainingOctadUOutputIsOctad 4 e = true ∧
          monsterNortonRemainingOctadUOutputChoice 4 e =
            monsterNortonCodeSeventeenInverseOctadChoice p.1 then
          (monsterNortonOctadPositiveInteger (monsterNortonCodeSeventeenInverseSign p.1 p.2)
            (monsterNortonRemainingOctadUOutputSign 4 e) : ℝ) / 8 else 0) =
        ((if monsterNortonRemainingOctadUOutputIsOctad 4 e = true ∧
          monsterNortonRemainingOctadUOutputChoice 4 e =
            monsterNortonCodeSeventeenInverseOctadChoice p.1 then
          monsterNortonCodeSeventeenInverseCoefficientCache e *
            monsterNortonOctadPositiveInteger (monsterNortonCodeSeventeenInverseSign p.1 p.2)
              (monsterNortonRemainingOctadUOutputSign 4 e) else 0 : ℤ) : ℝ) / 64 := by
    split_ifs <;> push_cast <;> ring
  simp_rw [he]
  rw [← Finset.sum_div, ← Int.cast_sum]
  change (monsterNortonCodeSeventeenInverseShortRead p : ℝ) / 64 = _
  rw [monsterNortonCodeSeventeenInverseShortRead_coefficient]
  push_cast
  ring

private theorem sign_last (i : Fin 16) :
    qSign (golayLabelCoefficients (monsterNortonCodeSeventeenInverseSpinLabel i) 11) =
      if (monsterNortonCodeSeventeenInverseSpinLabel i).val < 2048 then (1 : ℝ) else -1 := by
  have h : ∀ i : Fin 16,
      golayLabelCoefficients (monsterNortonCodeSeventeenInverseSpinLabel i) 11 =
        (if (monsterNortonCodeSeventeenInverseSpinLabel i).val < 2048 then 0 else 1 : ZMod 2) := by
    decide +kernel
  rw [h]
  split_ifs <;> norm_num [qSign]

private theorem tensor_form (e : Fin 64) (p : Fin 16 × Fin 4) :
    griessForm (monsterNortonShortExtraPacket (monsterNortonRemainingOctadUOutput 4 e))
      (monsterNortonTensorUnit (monsterNortonCodeSeventeenInverseTensorIndex p).1
        (monsterNortonCodeSeventeenInverseTensorIndex p).2) =
      if monsterNortonRemainingOctadUOutputIsOctad 4 e ≠ true ∧
        (monsterNortonRemainingOctadUOutputOddCode 4 e).val =
          (monsterNortonCodeSeventeenInverseSpinLabel p.1).val % 2048 ∧
        monsterNortonRemainingOctadUOutputOddPosition 4 e =
          monsterNortonCodeSeventeenInverseColumns p.2 then
        ((if (monsterNortonCodeSeventeenInverseSpinLabel p.1).val < 2048 then (1 : ℤ) else -1) *
          (if (golayEncodedMask (monsterNortonRemainingOctadUOutputOddCode 4 e).val).testBit
            (monsterNortonCodeSeventeenInverseColumns p.2).val then -1 else 1) : ℝ) / Real.sqrt 2
      else 0 := by
  unfold monsterNortonRemainingOctadUOutput monsterNortonCodeSeventeenInverseTensorIndex
  by_cases h : monsterNortonRemainingOctadUOutputIsOctad 4 e = true
  · simp only [h, ite_true, ne_eq, not_true_eq_false, false_and, ite_false]
    exact monsterNortonOctadExtra_tensor_form _ _ _ _
  · simp only [h, Bool.false_eq_true, ite_false, ne_eq, not_false_eq_true, true_and]
    rw [monsterNortonOddExtra_tensor_form, sign_last]
    have hd : spinDictionaryCode
        (golayLabelCoefficients (monsterNortonCodeSeventeenInverseSpinLabel p.1)) =
          monsterNortonRemainingOctadUOutputOddCode 4 e ↔
        (monsterNortonRemainingOctadUOutputOddCode 4 e).val =
          (monsterNortonCodeSeventeenInverseSpinLabel p.1).val % 2048 := by
      simp only [spinDictionaryCode, spinDictionaryLabel_coeff, Fin.ext_iff]
      exact eq_comm
    simp only [hd]
    by_cases hp : monsterNortonCodeSeventeenInverseColumns p.2 =
        monsterNortonRemainingOctadUOutputOddPosition 4 e
    · simp only [hp, true_and, and_true, Int.cast_ite, Int.cast_one, Int.cast_neg]
    · simp [hp, Ne.symm hp]

/-- Every whole inverse-sixth tensor pairing is its exact certified source coefficient. -/
theorem monsterNortonCodeSeventeenInverseHalf_tensor_form (p : Fin 16 × Fin 4) :
    griessForm (monsterNortonRemainingOctadInverseSixthPacket 4)
      (monsterNortonTensorUnit (monsterNortonCodeSeventeenInverseTensorIndex p).1
        (monsterNortonCodeSeventeenInverseTensorIndex p).2) =
        (monsterNortonCodeSeventeenInverseTensorCoefficient p : ℝ) / (32 * Real.sqrt 2) := by
  rw [monsterNortonCodeSeventeenInverseActualPacket_actual]
  unfold monsterNortonCodeSeventeenInverseActualPacket
  rw [map_sum]
  simp only [LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, tensor_form]
  have he (e : Fin 64) :
      (monsterNortonCodeSeventeenInverseCoefficientCache e : ℝ) / 8 *
        (if monsterNortonRemainingOctadUOutputIsOctad 4 e ≠ true ∧
          (monsterNortonRemainingOctadUOutputOddCode 4 e).val =
            (monsterNortonCodeSeventeenInverseSpinLabel p.1).val % 2048 ∧
          monsterNortonRemainingOctadUOutputOddPosition 4 e =
            monsterNortonCodeSeventeenInverseColumns p.2 then
          ((if (monsterNortonCodeSeventeenInverseSpinLabel p.1).val < 2048 then (1 : ℤ) else -1) *
            (if (golayEncodedMask (monsterNortonRemainingOctadUOutputOddCode 4 e).val).testBit
              (monsterNortonCodeSeventeenInverseColumns p.2).val then -1 else 1) : ℝ) /
                Real.sqrt 2 else 0) =
        ((if monsterNortonRemainingOctadUOutputIsOctad 4 e ≠ true ∧
          (monsterNortonRemainingOctadUOutputOddCode 4 e).val =
            (monsterNortonCodeSeventeenInverseSpinLabel p.1).val % 2048 ∧
          monsterNortonRemainingOctadUOutputOddPosition 4 e =
            monsterNortonCodeSeventeenInverseColumns p.2 then
          monsterNortonCodeSeventeenInverseCoefficientCache e *
            (if (monsterNortonCodeSeventeenInverseSpinLabel p.1).val < 2048 then 1 else -1) *
            (if (golayEncodedMask (monsterNortonRemainingOctadUOutputOddCode 4 e).val).testBit
              (monsterNortonCodeSeventeenInverseColumns p.2).val then -1 else 1) else 0 : ℤ) : ℝ) /
                (8 * Real.sqrt 2) := by
    split_ifs <;> push_cast <;> ring
  simp_rw [he]
  rw [← Finset.sum_div, ← Int.cast_sum]
  change (monsterNortonCodeSeventeenInverseTensorRead p : ℝ) / (8 * Real.sqrt 2) = _
  have hr : 4 * (monsterNortonCodeSeventeenInverseTensorRead p : ℝ) =
      (monsterNortonCodeSeventeenInverseTensorCoefficient p : ℝ) := by
    exact_mod_cast monsterNortonCodeSeventeenInverseTensorRead_coefficient p
  rw [← hr]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
