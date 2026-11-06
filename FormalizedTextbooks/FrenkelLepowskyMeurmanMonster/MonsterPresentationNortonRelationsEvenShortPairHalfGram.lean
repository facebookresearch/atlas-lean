/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Integer Gram entries between the actual seventh-step units and the sparse half candidate. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortPairHalfPacket
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortPairHalfSeventh
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortSecondHalfGram
@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
/-- Integer Gram entries, scaled by eight, against the finite sparse candidate units. -/
def monsterNortonPairHalfGram (k : Fin 12) (e : Fin 64) : NortonPairHalfIndex → ℤ
  | Sum.inl i =>
    if monsterNortonEvenShortInverseUKind (monsterNortonPairHalfBasisIndex k) e = 0 ∧
      monsterNortonEvenShortInverseUPairFirst (monsterNortonPairHalfBasisIndex k) e =
        monsterNortonPairHalfPairFirst k i ∧
      monsterNortonEvenShortInverseUPairSecond (monsterNortonPairHalfBasisIndex k) e =
     (monsterNortonPairHalfPairSecond k) i
    then 8 else 0
  | Sum.inr (Sum.inl i) =>
    if monsterNortonEvenShortInverseUKind (monsterNortonPairHalfBasisIndex k) e = 0 ∧
      monsterNortonEvenShortInverseUPairFirst (monsterNortonPairHalfBasisIndex k) e =
        monsterNortonPairHalfPairFirst k i ∧
      monsterNortonEvenShortInverseUPairSecond (monsterNortonPairHalfBasisIndex k) e =
     (monsterNortonPairHalfPairSecond k) i
    then if monsterNortonEvenShortInverseUPairSign (monsterNortonPairHalfBasisIndex k) e =
     0 then 8 else -8 else 0
  | Sum.inr (Sum.inr (d, f)) =>
    if monsterNortonEvenShortInverseUKind (monsterNortonPairHalfBasisIndex k) e = 1 ∧
      monsterNortonEvenShortInverseUOctadCodes
        (monsterNortonEvenShortInverseUOctadSlot (monsterNortonPairHalfBasisIndex k) e) =
        (monsterNortonPairHalfOctadCode k) d
    then monsterNortonOctadPositiveInteger ((monsterNortonPairHalfOctadSign k) d f)
      (monsterNortonEvenShortInverseUOctadSign (monsterNortonPairHalfBasisIndex k) e) else 0
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
theorem monsterNortonPairHalfGram_actual (k : Fin 12) (e : Fin 64) (i : NortonPairHalfIndex) :
    griessForm (monsterNortonEvenShortPairHalfSeventhTerm k e)
      ((monsterNortonPairHalfVector k) i) = ((monsterNortonPairHalfGram k) e i : ℝ) / 8 := by
  have hp (j : Fin 8) := monsterNortonOrderedPairIndex_eq_iff
    (monsterNortonEvenShortInverseUPairFirst (monsterNortonPairHalfBasisIndex k) e)
    (monsterNortonEvenShortInverseUPairSecond (monsterNortonPairHalfBasisIndex k) e)
    ((monsterNortonPairHalfPairFirst k) j) ((monsterNortonPairHalfPairSecond k) j)
    (monsterNortonEvenShortInverseUPair_lt (monsterNortonPairHalfBasisIndex k) e)
    (monsterNortonPairHalfPair_lt k j)
  have hcases := (monsterNortonEvenShortPairHalfOutput_pair_or_octad k) e
  by_cases hk : monsterNortonEvenShortInverseUKind (monsterNortonPairHalfBasisIndex k) e = 0
  · rcases i with i | (i | ⟨d, f⟩) <;>
      simp only [monsterNortonEvenShortPairHalfSeventhTerm, hk, ite_true,
        monsterNortonPairHalfVector, monsterNortonPairHalfGram, true_and]
    · simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        smul_eq_mul, monsterNortonForm_ABC_ABC]
      simp only [monsterNortonPairHalfPairIndex]
      simp only [hp]
      norm_num
      split_ifs <;> norm_num
    · simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        smul_eq_mul, monsterNortonForm_ABC_ABC]
      simp only [monsterNortonPairHalfPairIndex]
      simp only [hp]
      norm_num
      split_ifs <;> norm_num
    · simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        smul_eq_mul, ABC_octad, mul_zero, add_zero]
      norm_num
  · have h1 := hcases.resolve_left hk
    rcases i with i | (i | ⟨d, f⟩) <;>
      simp only [monsterNortonEvenShortPairHalfSeventhTerm, hk, ite_false,
        monsterNortonPairHalfVector, monsterNortonPairHalfGram, false_and]
    · simp only [monsterNortonForm_octad_ABC, Int.cast_zero, zero_div]
    · simp only [monsterNortonForm_octad_ABC, Int.cast_zero, zero_div]
    · rw [monsterNortonForm_octad_unit_code, monsterNortonOctadTriality_single,
        monsterNortonOctadPositiveInteger_actual]
      simp only [h1, true_and, mul_one]
      split_ifs <;> simp
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
