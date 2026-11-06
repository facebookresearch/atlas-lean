/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual whole forward-seventh packet reads on the normalized code-twentyone support. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyOneForwardCoefficients
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyOneForwardCoefficientActual
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortExtraTensorPairings

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem displayCodes_injective :
    Function.Injective monsterNortonEvenShortInverseUOctadCodes := by
  apply StrictMono.injective
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 93, monsterNortonEvenShortInverseUOctadCodes i.castSucc <
      monsterNortonEvenShortInverseUOctadCodes i.succ := by decide +kernel
  exact hc

private theorem kind_cases (e : Fin 64) :
    monsterNortonEvenShortInverseUKind 21 e = 1 ∨
      monsterNortonEvenShortInverseUKind 21 e = 2 := by
  revert e
  decide +kernel

private theorem short_form (e : Fin 64) (p : Fin 8 × Fin 32) :
    griessForm (monsterNortonShortExtraPacket (monsterNortonEvenShortInverseUOutput 21 e))
      (monsterNortonPureShort (monsterNortonCodeTwentyOneForwardShortIndex p)) =
      if monsterNortonEvenShortInverseUKind 21 e = 1 ∧
        monsterNortonEvenShortInverseUOctadSlot 21 e =
          monsterNortonCodeTwentyOneForwardOctadChoice p.1 then
        (monsterNortonOctadPositiveInteger (monsterNortonCodeTwentyOneForwardSign p.1 p.2)
          (monsterNortonEvenShortInverseUOctadSign 21 e) : ℝ) / 8
      else 0 := by
  unfold monsterNortonEvenShortInverseUOutput monsterNortonCodeTwentyOneForwardShortIndex
  rcases kind_cases e with h | h
  · simp only [h, show (1 : Fin 3) ≠ 0 from by decide, ite_false, ite_true, true_and]
    rw [monsterNortonOctadExtra_octad_form]
    simp only [displayCodes_injective.eq_iff]
  · simp only [h, show (2 : Fin 3) ≠ 0 from by decide,
      show (2 : Fin 3) ≠ 1 from by decide, ite_false, false_and]
    exact monsterNortonOddExtra_short_form _ _ _

/-- Every whole forward-seventh short pairing is its exact certified source coefficient. -/
theorem monsterNortonCodeTwentyOneForwardHalf_short_form (p : Fin 8 × Fin 32) :
    griessForm (monsterNortonCodeTwentyOneForwardActualPacket)
      (monsterNortonPureShort (monsterNortonCodeTwentyOneForwardShortIndex p)) =
        (monsterNortonCodeTwentyOneForwardShortCoefficient p.1 p.2 : ℝ) / 32 := by
  unfold monsterNortonCodeTwentyOneForwardActualPacket
  rw [map_sum]
  simp only [LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, short_form]
  have he (e : Fin 64) :
      (monsterNortonCodeTwentyOneForwardCoefficientCache e : ℝ) / 8 *
        (if monsterNortonEvenShortInverseUKind 21 e = 1 ∧
          monsterNortonEvenShortInverseUOctadSlot 21 e =
            monsterNortonCodeTwentyOneForwardOctadChoice p.1 then
          (monsterNortonOctadPositiveInteger (monsterNortonCodeTwentyOneForwardSign p.1 p.2)
            (monsterNortonEvenShortInverseUOctadSign 21 e) : ℝ) / 8 else 0) =
        ((if monsterNortonEvenShortInverseUKind 21 e = 1 ∧
          monsterNortonEvenShortInverseUOctadSlot 21 e =
            monsterNortonCodeTwentyOneForwardOctadChoice p.1 then
          monsterNortonCodeTwentyOneForwardCoefficientCache e *
            monsterNortonOctadPositiveInteger (monsterNortonCodeTwentyOneForwardSign p.1 p.2)
              (monsterNortonEvenShortInverseUOctadSign 21 e) else 0 : ℤ) : ℝ) / 64 := by
    split_ifs <;> push_cast <;> ring
  simp_rw [he]
  rw [← Finset.sum_div, ← Int.cast_sum]
  change (monsterNortonCodeTwentyOneForwardShortRead p : ℝ) / 64 = _
  rw [monsterNortonCodeTwentyOneForwardShortRead_coefficient]
  push_cast
  ring

private theorem sign_last (i : Fin 16) :
    qSign (golayLabelCoefficients (monsterNortonCodeTwentyOneForwardSpinLabel i) 11) =
      if (monsterNortonCodeTwentyOneForwardSpinLabel i).val < 2048 then (1 : ℝ) else -1 := by
  have h : ∀ i : Fin 16,
      golayLabelCoefficients (monsterNortonCodeTwentyOneForwardSpinLabel i) 11 =
        (if (monsterNortonCodeTwentyOneForwardSpinLabel i).val < 2048 then 0 else 1 : ZMod 2) := by
    decide +kernel
  rw [h]
  split_ifs <;> norm_num [qSign]

private theorem tensor_form (e : Fin 64) (p : Fin 16 × Fin 4) :
    griessForm (monsterNortonShortExtraPacket (monsterNortonEvenShortInverseUOutput 21 e))
      (monsterNortonTensorUnit (monsterNortonCodeTwentyOneForwardTensorIndex p).1
        (monsterNortonCodeTwentyOneForwardTensorIndex p).2) =
      if monsterNortonEvenShortInverseUKind 21 e = 2 ∧
        (monsterNortonEvenShortInverseUOddCode 21 e).val =
          (monsterNortonCodeTwentyOneForwardSpinLabel p.1).val % 2048 ∧
        monsterNortonEvenShortInverseUOddPosition 21 e =
          monsterNortonCodeTwentyOneForwardColumns p.2 then
        ((if (monsterNortonCodeTwentyOneForwardSpinLabel p.1).val < 2048 then (1 : ℤ) else -1) *
          (if (golayEncodedMask (monsterNortonEvenShortInverseUOddCode 21 e).val).testBit
            (monsterNortonCodeTwentyOneForwardColumns p.2).val then -1 else 1) : ℝ) / Real.sqrt 2
      else 0 := by
  unfold monsterNortonEvenShortInverseUOutput monsterNortonCodeTwentyOneForwardTensorIndex
  rcases kind_cases e with h | h
  · simp only [h, show (1 : Fin 3) ≠ 0 from by decide,
      show (1 : Fin 3) ≠ 2 from by decide, ite_true, ite_false, false_and]
    exact monsterNortonOctadExtra_tensor_form _ _ _ _
  · simp only [h, show (2 : Fin 3) ≠ 0 from by decide,
      show (2 : Fin 3) ≠ 1 from by decide, ite_false, true_and]
    rw [monsterNortonOddExtra_tensor_form, sign_last]
    have hd : spinDictionaryCode
        (golayLabelCoefficients (monsterNortonCodeTwentyOneForwardSpinLabel p.1)) =
          monsterNortonEvenShortInverseUOddCode 21 e ↔
        (monsterNortonEvenShortInverseUOddCode 21 e).val =
          (monsterNortonCodeTwentyOneForwardSpinLabel p.1).val % 2048 := by
      simp only [spinDictionaryCode, spinDictionaryLabel_coeff, Fin.ext_iff]
      exact eq_comm
    simp only [hd]
    by_cases hp : monsterNortonCodeTwentyOneForwardColumns p.2 =
        monsterNortonEvenShortInverseUOddPosition 21 e
    · simp only [hp, true_and, and_true, Int.cast_ite, Int.cast_one, Int.cast_neg]
    · simp [hp, Ne.symm hp]

/-- Every whole forward-seventh tensor pairing is its exact certified source coefficient. -/
theorem monsterNortonCodeTwentyOneForwardHalf_tensor_form (p : Fin 16 × Fin 4) :
    griessForm (monsterNortonCodeTwentyOneForwardActualPacket)
      (monsterNortonTensorUnit (monsterNortonCodeTwentyOneForwardTensorIndex p).1
        (monsterNortonCodeTwentyOneForwardTensorIndex p).2) =
        (monsterNortonCodeTwentyOneForwardTensorCoefficient p : ℝ) / (32 * Real.sqrt 2) := by
  unfold monsterNortonCodeTwentyOneForwardActualPacket
  rw [map_sum]
  simp only [LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, tensor_form]
  have he (e : Fin 64) :
      (monsterNortonCodeTwentyOneForwardCoefficientCache e : ℝ) / 8 *
        (if monsterNortonEvenShortInverseUKind 21 e = 2 ∧
          (monsterNortonEvenShortInverseUOddCode 21 e).val =
            (monsterNortonCodeTwentyOneForwardSpinLabel p.1).val % 2048 ∧
          monsterNortonEvenShortInverseUOddPosition 21 e =
            monsterNortonCodeTwentyOneForwardColumns p.2 then
          ((if (monsterNortonCodeTwentyOneForwardSpinLabel p.1).val < 2048 then (1 : ℤ) else -1) *
            (if (golayEncodedMask (monsterNortonEvenShortInverseUOddCode 21 e).val).testBit
              (monsterNortonCodeTwentyOneForwardColumns p.2).val then -1 else 1) : ℝ) /
                Real.sqrt 2 else 0) =
        ((if monsterNortonEvenShortInverseUKind 21 e = 2 ∧
          (monsterNortonEvenShortInverseUOddCode 21 e).val =
            (monsterNortonCodeTwentyOneForwardSpinLabel p.1).val % 2048 ∧
          monsterNortonEvenShortInverseUOddPosition 21 e =
            monsterNortonCodeTwentyOneForwardColumns p.2 then
          monsterNortonCodeTwentyOneForwardCoefficientCache e *
            (if (monsterNortonCodeTwentyOneForwardSpinLabel p.1).val < 2048 then 1 else -1) *
            (if (golayEncodedMask (monsterNortonEvenShortInverseUOddCode 21 e).val).testBit
              (monsterNortonCodeTwentyOneForwardColumns p.2).val then -1 else 1) else 0 : ℤ) : ℝ) /
                (8 * Real.sqrt 2) := by
    split_ifs <;> push_cast <;> ring
  simp_rw [he]
  rw [← Finset.sum_div, ← Int.cast_sum]
  change (monsterNortonCodeTwentyOneForwardTensorRead p : ℝ) / (8 * Real.sqrt 2) = _
  have hr : 4 * (monsterNortonCodeTwentyOneForwardTensorRead p : ℝ) =
      (monsterNortonCodeTwentyOneForwardTensorCoefficient p : ℝ) := by
    exact_mod_cast monsterNortonCodeTwentyOneForwardTensorRead_coefficient p
  rw [← hr]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
