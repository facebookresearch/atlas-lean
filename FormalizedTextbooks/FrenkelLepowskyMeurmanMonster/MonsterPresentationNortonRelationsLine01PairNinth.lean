/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The entire actual ninth first-pair word state, including every matrix and short coordinate. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairNinthMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairNinthPairCancellation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairEighthOctadPacket

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem conditional_add {E : Type*} [AddZeroClass E]
    (p : Prop) [Decidable p] (a b : E) :
    (if p then a + b else 0) = (if p then a else 0) + (if p then b else 0) := by
  by_cases h : p <;> simp [h]

/-- The full true short packet splits exactly into its original pair and octad contributions. -/
theorem monsterNortonLine01PairEighthShortPacket_split :
    monsterNortonLine01PairEighthShortPacket =
      (∑ k : Fin 240, if monsterNortonLine01PairEighthIsPair k then
        ((monsterNortonLine01PairEighthCoefficient k : ℝ) / 16) •
          monsterNortonPureShort (monsterNortonLine01PairEighthShortOutput k) else 0) +
      ∑ k : Fin 240, if monsterNortonLine01PairEighthIsPair k then 0 else
        ((monsterNortonLine01PairEighthCoefficient k : ℝ) / 16) •
          monsterNortonPureShort (monsterNortonLine01PairEighthShortOutput k) := by
  rw [monsterNortonLine01PairEighthShortPacket_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hp : monsterNortonLine01PairEighthIsPair k = true <;> simp [hp]

private theorem inversePairTerm (k : Fin 240) :
    sExtra.symm (if monsterNortonLine01PairEighthIsPair k then
      ((monsterNortonLine01PairEighthCoefficient k : ℝ) / 16) •
        monsterNortonPureShort (monsterNortonLine01PairEighthShortOutput k) else 0) =
      if monsterNortonLine01PairEighthIsPair k then
        ((monsterNortonLine01PairEighthCoefficient k : ℝ) / 32) •
          trialityABCBasis 1 (monsterNortonLine01PairEighthPhysicalPair k) +
        (((monsterNortonLine01PairEighthCoefficient k *
          (if monsterNortonLine01PairEighthPairFamily k = 0 then (1 : ℤ) else -1) : ℤ) : ℝ) /
            32) • trialityABCBasis 0 (monsterNortonLine01PairEighthPhysicalPair k) else 0 := by
  by_cases hp : monsterNortonLine01PairEighthIsPair k = true
  · rw [ite_eq_left hp, ite_eq_left hp, map_smul]
    unfold monsterNortonLine01PairEighthShortOutput
    rw [ite_eq_left hp, monsterNortonPairShort_extra_inverse, smul_add, smul_smul,
      smul_smul]
    change _ • trialityABCBasis 1 (monsterNortonLine01PairEighthPhysicalPair k) +
      _ • trialityABCBasis 0 (monsterNortonLine01PairEighthPhysicalPair k) = _
    congr 1
    · congr 1
      ring
    · by_cases hs : monsterNortonLine01PairEighthPairFamily k = 0
      · simp only [ite_eq_left hs, mul_one]
        congr 1
        ring
      · simp only [ite_eq_right hs, Int.cast_neg, mul_neg, mul_one]
        congr 1
        ring
  · rw [ite_eq_right hp, ite_eq_right hp, map_zero]

/-- Inverse triality sends the entire pair packet to its remaining matrix-only contribution. -/
theorem monsterNortonLine01PairNinth_inverse_pair_packet :
    sExtra.symm (∑ k : Fin 240, if monsterNortonLine01PairEighthIsPair k then
      ((monsterNortonLine01PairEighthCoefficient k : ℝ) / 16) •
        monsterNortonPureShort (monsterNortonLine01PairEighthShortOutput k) else 0) =
      ∑ k : Fin 240, if monsterNortonLine01PairEighthIsPair k then
        (((monsterNortonLine01PairEighthCoefficient k *
          (if monsterNortonLine01PairEighthPairFamily k = 0 then (1 : ℤ) else -1) : ℤ) : ℝ) /
            32) • trialityABCBasis 0 (monsterNortonLine01PairEighthPhysicalPair k) else 0 := by
  rw [map_sum]
  simp only [inversePairTerm, conditional_add, Finset.sum_add_distrib]
  rw [monsterNortonLine01PairNinth_pair_short_cancel, zero_add]

/-- The entire ninth actual word state has its exact forward-U matrix and two surviving octads. -/
theorem monsterNortonLine01PairNinth_actual :
    sExtra.symm (y555NortonActualU.val monsterNortonLine01PairAfterSeventh) =
      (-1 / 2 : ℝ) • y555NortonActualU.val
        (trialityABCBasis 0 (monsterNortonLine01AdjacentPair 0)) +
      ∑ a : Fin 2, (-1 / 2 : ℝ) • monsterNortonPureShort
        (Sum.inr (Sum.inl (monsterNortonLine01PairEighthBlockOctad a,
          monsterNortonLine01PairNinthOctadTarget a))) := by
  rw [monsterNortonLine01PairEighth_diagonal, map_add,
    monsterNortonDiagonal_extra_inverse, monsterNortonLine01PairEighthShortPacket_split,
    map_add, monsterNortonLine01PairNinth_inverse_pair_packet,
    monsterNortonLine01PairNinth_octad_packet, ← add_assoc,
    monsterNortonLine01PairNinth_matrix_vector_U]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
