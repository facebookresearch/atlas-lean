/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The entire original-coordinate expansion after seven literal first-pair operators. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairSeventhOctadRegroup

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual phase-complete coefficient has exactly its integer numerator over eight. -/
theorem monsterNortonLine01PairActualCoefficient_integer (e : Fin 64) :
    monsterNortonLine01PairActualCoefficient e =
      (monsterNortonLine01PairSixthNumerator e : ℝ) / 8 := by
  simp only [monsterNortonLine01PairActualCoefficient, monsterNortonLine01PairSixthNumerator,
    Int.cast_mul, monsterNortonLine01PairPhaseSign_cast]
  ring

private theorem sourceTermSplit (e : Fin 64) :
    monsterNortonLine01PairActualCoefficient e • monsterNortonLine01PairSeventhTerm e =
      (if monsterNortonLine01PairInverseIsPair e then
        ((monsterNortonLine01PairSixthNumerator e : ℝ) / 16) •
          trialityABCBasis 0 (monsterNortonLine01PairInversePhysicalPair e) +
        (((monsterNortonLine01PairSixthNumerator e *
          (if monsterNortonLine01PairInversePairSign e = 0 then (1 : ℤ) else -1) : ℤ) : ℝ) /
            16) • trialityABCBasis 2 (monsterNortonLine01PairInversePhysicalPair e)
        else 0) +
      (if monsterNortonLine01PairInverseIsPair e then 0 else
        monsterNortonLine01PairActualCoefficient e • monsterNortonOctadShortVector
          (monsterNortonLine01PairBlockOctad (monsterNortonLine01PairInverseOctadSlot e))
          (trialityOctadAction (Pi.single (monsterNortonLine01PairInverseOctadSign e) 1))) := by
  unfold monsterNortonLine01PairSeventhTerm
  by_cases hp : monsterNortonLine01PairInverseIsPair e = true
  · simp only [ite_eq_left hp, add_zero]
    rw [monsterNortonLine01PairActualCoefficient_integer, smul_add, smul_smul, smul_smul]
    congr 1
    · congr 1
      ring
    · by_cases hs : monsterNortonLine01PairInversePairSign e = 0
      · simp only [ite_eq_left hs, mul_one]
        congr 1
        ring
      · simp only [ite_eq_right hs, Int.cast_neg, mul_neg,
          mul_one]
        congr 1
        ring
  · simp only [ite_eq_right hp, zero_add]
    rfl

/-- The full actual seventh vector consists of eight A, eight C, and fourteen octad blocks. -/
theorem monsterNortonLine01PairSeventh_expansion :
    monsterNortonLine01PairAfterSeventh =
      ((∑ k : Fin 8, ((monsterNortonLine01PairSeventhMatrixNumerator k : ℝ) / 16) •
          trialityABCBasis 0 (monsterNortonLine01AdjacentPair k)) +
        ∑ k : Fin 8, (-1 / 16 : ℝ) • trialityABCBasis 2 (monsterNortonLine01AdjacentPair k)) +
      ∑ a : Fin 14, monsterNortonOctadShortVector (monsterNortonLine01PairBlockOctad a)
        (fun r => (monsterNortonLine01PairSeventhOctadNumerator a r : ℝ) / 16) := by
  rw [monsterNortonLine01PairAfterSeventh]
  change (∑ e : Fin 64,
    monsterNortonLine01PairActualCoefficient e • monsterNortonLine01PairSeventhTerm e) = _
  simp only [sourceTermSplit, Finset.sum_add_distrib]
  rw [monsterNortonLine01PairSeventh_pair_regroup, monsterNortonLine01PairSeventh_octad_regroup]

/-- Each whole original octad block can equivalently be replaced by its sixteen supported units. -/
theorem monsterNortonLine01PairSeventh_expansion_compact :
    monsterNortonLine01PairAfterSeventh =
      ((∑ k : Fin 8, ((monsterNortonLine01PairSeventhMatrixNumerator k : ℝ) / 16) •
          trialityABCBasis 0 (monsterNortonLine01AdjacentPair k)) +
        ∑ k : Fin 8, (-1 / 16 : ℝ) • trialityABCBasis 2 (monsterNortonLine01AdjacentPair k)) +
      ∑ a : Fin 14, ∑ j : Fin 16,
        ((monsterNortonLine01PairSeventhOctadSupportCoefficient a j : ℝ) / 16) •
          monsterNortonPureShort (Sum.inr (Sum.inl
            (monsterNortonLine01PairBlockOctad a,
              monsterNortonLine01PairSeventhOctadSupport a j))) := by
  rw [monsterNortonLine01PairSeventh_expansion]
  simp only [monsterNortonLine01PairSeventhOctad_compact]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
