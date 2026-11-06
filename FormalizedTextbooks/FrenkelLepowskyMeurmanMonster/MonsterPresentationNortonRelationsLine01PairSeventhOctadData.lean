/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The checked compact octad coordinates of the actual first pair-short seventh state. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairSeventhData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairSeventhOctadCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem term_scalar (e : Fin 64) (a : Fin 14) (r : Fin 64) :
    (((monsterNortonLine01PairOctadInverseNumerator e : ℝ) / 8) *
      qSign (monsterNortonLine01PairOctadVPhase e) *
        qSign (monsterNortonLine01PairInverseVPhase e)) *
      (if monsterNortonLine01PairInverseIsPair e then 0
       else if monsterNortonLine01PairInverseOctadSlot e = a then
         monsterNortonOctadTrialityCoefficient r (monsterNortonLine01PairInverseOctadSign e)
       else 0) =
      ((if monsterNortonLine01PairInverseIsPair e then 0
        else if monsterNortonLine01PairInverseOctadSlot e = a then
          monsterNortonLine01PairSixthNumerator e *
            (if trialityBitWeight8 (trialityEvenMask r) / 2 % 2 = 0 then (1 : ℤ) else -1) *
              trialityHadamard r (monsterNortonLine01PairInverseOctadSign e)
        else 0 : ℤ) : ℝ) / 64 := by
  by_cases hp : monsterNortonLine01PairInverseIsPair e = true
  · simp only [ite_eq_left hp, mul_zero, Int.cast_zero, zero_div]
  · by_cases hs : monsterNortonLine01PairInverseOctadSlot e = a
    · simp only [ite_eq_right hp, ite_eq_left hs, monsterNortonOctadTrialityCoefficient,
        monsterNortonLine01PairSixthNumerator, Int.cast_mul,
        monsterNortonLine01PairPhaseSign_cast, Int.cast_ite, Int.cast_one, Int.cast_neg]
      split_ifs <;> ring
    · simp only [ite_eq_right hp, ite_eq_right hs, mul_zero, Int.cast_zero, zero_div]

/-- Every original reached octad coordinate is its checked integer numerator divided by sixteen. -/
theorem monsterNortonLine01PairSeventh_octad_data (a : Fin 14) (r : Fin 64) :
    monsterNortonShortProjection monsterNortonLine01PairAfterSeventh
      (Sum.inr (Sum.inl (monsterNortonLine01PairBlockOctad a, r))) =
        (monsterNortonLine01PairSeventhOctadNumerator a r : ℝ) / 16 := by
  rw [monsterNortonLine01PairAfterSeventh, map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    monsterNortonLine01PairSeventhTerm_octad, monsterNortonOctadTriality_single, mul_one]
  calc
    _ = ∑ e : Fin 64,
        ((if monsterNortonLine01PairInverseIsPair e then 0
          else if monsterNortonLine01PairInverseOctadSlot e = a then
            monsterNortonLine01PairSixthNumerator e *
              (if trialityBitWeight8 (trialityEvenMask r) / 2 % 2 = 0 then (1 : ℤ) else -1) *
                trialityHadamard r (monsterNortonLine01PairInverseOctadSign e)
          else 0 : ℤ) : ℝ) / 64 := by
      apply Finset.sum_congr rfl
      intro e _
      exact term_scalar e a r
    _ = ((∑ e : Fin 64,
        if monsterNortonLine01PairInverseIsPair e then 0
        else if monsterNortonLine01PairInverseOctadSlot e = a then
          monsterNortonLine01PairSixthNumerator e *
            (if trialityBitWeight8 (trialityEvenMask r) / 2 % 2 = 0 then (1 : ℤ) else -1) *
              trialityHadamard r (monsterNortonLine01PairInverseOctadSign e)
        else 0 : ℤ) : ℝ) / 64 := by
      rw [← Finset.sum_div, Int.cast_sum]
    _ = (monsterNortonLine01PairSeventhOctadNumerator a r : ℝ) / 16 := by
      rw [monsterNortonLine01PairSeventhOctadNumerator_certificate]
      push_cast
      ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
