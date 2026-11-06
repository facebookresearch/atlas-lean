/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Integer Gram entries between the actual seventh-step units and the sparse half candidate. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortSecondHalfPacket
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortSecondSeventh
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortCoefficientInteger

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The positive source octad Fourier coefficient before its denominator eight. -/
def monsterNortonOctadPositiveInteger (r s : Fin 64) : ℤ :=
  (if trialityBitWeight8 (trialityEvenMask r) / 2 % 2 = 0 then 1 else -1) *
    trialityHadamard r s

/-- This integer numerator retains the exact actual positive triality coefficient. -/
theorem monsterNortonOctadPositiveInteger_actual (r s : Fin 64) :
    monsterNortonOctadTrialityCoefficient r s =
      (monsterNortonOctadPositiveInteger r s : ℝ) / 8 := by
  unfold monsterNortonOctadTrialityCoefficient monsterNortonOctadPositiveInteger
  split_ifs <;> simp

/-- Integer Gram entries, scaled by eight, against the finite sparse candidate units. -/
def monsterNortonSecondHalfGram (e : Fin 64) : NortonSecondHalfIndex → ℤ
  | Sum.inl i =>
    if monsterNortonEvenShortInverseUKind 1 e = 0 ∧
      monsterNortonEvenShortInverseUPairFirst 1 e = monsterNortonSecondHalfPairFirst i ∧
      monsterNortonEvenShortInverseUPairSecond 1 e = monsterNortonSecondHalfPairSecond i
    then 8 else 0
  | Sum.inr (Sum.inl i) =>
    if monsterNortonEvenShortInverseUKind 1 e = 0 ∧
      monsterNortonEvenShortInverseUPairFirst 1 e = monsterNortonSecondHalfPairFirst i ∧
      monsterNortonEvenShortInverseUPairSecond 1 e = monsterNortonSecondHalfPairSecond i
    then if monsterNortonEvenShortInverseUPairSign 1 e = 0 then 8 else -8 else 0
  | Sum.inr (Sum.inr (d, f)) =>
    if monsterNortonEvenShortInverseUKind 1 e = 1 ∧
      monsterNortonEvenShortInverseUOctadCodes (monsterNortonEvenShortInverseUOctadSlot 1 e) =
        monsterNortonSecondHalfOctadCode d
    then monsterNortonOctadPositiveInteger (monsterNortonSecondHalfOctadSign d f)
      (monsterNortonEvenShortInverseUOctadSign 1 e) else 0

private theorem ABC_octad (s : Fin 3) (p : Fin 276) (d : Fin 759) (e : Fin 64) :
    griessForm (trialityABCBasis s p)
      (monsterNortonPureShort (Sum.inr (Sum.inl (d, e)))) = 0 := by
  have hs : griessForm (trialityABCBasis s p)
      (monsterNortonPureShort (Sum.inr (Sum.inl (d, e)))) =
      griessForm (monsterNortonPureShort (Sum.inr (Sum.inl (d, e))))
        (trialityABCBasis s p) := by
    rw [griessForm_apply, griessForm_apply]
    unfold griessFormFun
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs]
  unfold monsterNortonPureShort
  rw [← monsterNortonOctadShortVector_single d e 1, monsterNortonForm_octad_ABC]

/-- Every displayed finite Gram entry is an equality in the actual Griess form. -/
theorem monsterNortonSecondHalfGram_actual (e : Fin 64) (i : NortonSecondHalfIndex) :
    griessForm (monsterNortonEvenShortSecondSeventhTerm e)
      (monsterNortonSecondHalfVector i) = (monsterNortonSecondHalfGram e i : ℝ) / 8 := by
  have hp (j : Fin 8) := monsterNortonOrderedPairIndex_eq_iff
    (monsterNortonEvenShortInverseUPairFirst 1 e)
    (monsterNortonEvenShortInverseUPairSecond 1 e)
    (monsterNortonSecondHalfPairFirst j) (monsterNortonSecondHalfPairSecond j)
    (monsterNortonEvenShortInverseUPair_lt 1 e) (monsterNortonSecondHalfPair_lt j)
  have hcases := monsterNortonEvenShortSecondOutput_pair_or_octad e
  by_cases hk : monsterNortonEvenShortInverseUKind 1 e = 0
  · rcases i with i | (i | ⟨d, f⟩) <;>
      simp only [monsterNortonEvenShortSecondSeventhTerm, hk, ite_true,
        monsterNortonSecondHalfVector, monsterNortonSecondHalfGram, true_and]
    · simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        smul_eq_mul, monsterNortonForm_ABC_ABC]
      simp only [monsterNortonSecondHalfPairIndex]
      simp only [hp]
      norm_num
      split_ifs <;> norm_num
    · simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        smul_eq_mul, monsterNortonForm_ABC_ABC]
      simp only [monsterNortonSecondHalfPairIndex]
      simp only [hp]
      norm_num
      split_ifs <;> norm_num
    · simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        smul_eq_mul, ABC_octad, mul_zero, add_zero]
      norm_num
  · have h1 := hcases.resolve_left hk
    rcases i with i | (i | ⟨d, f⟩) <;>
      simp only [monsterNortonEvenShortSecondSeventhTerm, hk, ite_false,
        monsterNortonSecondHalfVector, monsterNortonSecondHalfGram, false_and]
    · simp only [monsterNortonForm_octad_ABC, Int.cast_zero, zero_div]
    · simp only [monsterNortonForm_octad_ABC, Int.cast_zero, zero_div]
    · rw [monsterNortonForm_octad_unit_code, monsterNortonOctadTriality_single,
        monsterNortonOctadPositiveInteger_actual]
      simp only [h1, true_and, mul_one]
      split_ifs <;> simp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
