/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual whole matrix and short Gram entries for the code-three inverse packet. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOctadThreeInverseGramData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsMatrixShortExtraPairings
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortExtraPairings

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The complete actual inverse packet equals its signed integer source expansion. -/
theorem monsterNortonOctadThreeInverseSixthPacket_sum :
    monsterNortonOctadThreeInverseSixthPacket =
      ∑ e : Fin 64, ((monsterNortonOctadThreeInverseIntegerCoefficient e : ℝ) / 8) •
        monsterNortonShortExtraPacket (monsterNortonOctadThreeUOutput e) := by
  unfold monsterNortonOctadThreeInverseSixthPacket
  rw [Finset.smul_sum]
  simp only [smul_smul, monsterNortonOctadThreeInverseIntegerCoefficient_actual]

private theorem matrix_symmetric (p : Fin 8) :
    ∀ i j, conwayMatrixAction monsterNortonUFiber.val.2
      (trialityPairMatrix (monsterNortonPairHalfPairIndex 11 p)) i j =
        conwayMatrixAction monsterNortonUFiber.val.2
          (trialityPairMatrix (monsterNortonPairHalfPairIndex 11 p)) j i :=
  conwayMatrixAction_symmetric _ _ (trialityPairMatrix_symmetric _)

/-- Every displayed matrix Gram numerator pairs entire actual physical vectors. -/
theorem monsterNortonOctadThreeInverseMatrixGram_actual (p : Fin 8) (e : Fin 64) :
    griessForm (griessConwayDecode (conwayMatrixAction monsterNortonUFiber.val.2
      (trialityPairMatrix (monsterNortonPairHalfPairIndex 11 p)), (0, 0)))
      (monsterNortonShortExtraPacket (monsterNortonOctadThreeUOutput e)) =
        (monsterNortonOctadThreeInverseMatrixGram p e : ℝ) / 16 := by
  rw [monsterNortonOctadThreeUOutput_dictionary]
  unfold monsterNortonOctadThreeInverseMatrixGram
  by_cases hk : monsterNortonOctadThreeUOutputKind e = 0
  · simp only [hk, ite_true]
    rw [monsterNortonPureMatrix_pairExtra_form _ (matrix_symmetric p),
      monsterNortonUPairMatrix_coordinates]
    simp only [monsterNortonUPairMatrixNumerator, monsterNortonPairHalfPairIndex,
      griessPairIndex_coordinates, monsterNortonPairHalfPair_lt,
      monsterNortonOctadThreeUOutputPair_lt, ite_true]
  · simp only [hk, ite_false]
    rw [monsterNortonPureMatrix_octadExtra_form _ (matrix_symmetric p)]
    norm_num

/-- Every displayed short Gram numerator is its entire actual positive-triality pairing. -/
theorem monsterNortonOctadThreeInverseShortGram_actual (e : Fin 64)
    (i : NortonPairHalfShortIndex) :
    griessForm (monsterNortonShortExtraPacket (monsterNortonOctadThreeUOutput e))
      (monsterNortonPureShort (monsterNortonPairHalfUPoolOutput
        (monsterNortonPairHalfUPoolStorage 11 i))) =
      (monsterNortonOctadThreeInverseShortGram e i : ℝ) / 8 := by
  rw [monsterNortonOctadThreeUOutput_dictionary]
  unfold monsterNortonPairHalfUPoolOutput monsterNortonOctadThreeInverseShortGram
  by_cases hs : monsterNortonOctadThreeUOutputKind e = 0 <;>
    by_cases ht : monsterNortonPairHalfUPoolOutputKind
      (monsterNortonPairHalfUPoolStorage 11 i) = 0
  · simp only [hs, ht, ite_true, true_and]
    rw [monsterNortonPairExtra_pair_form]
    simp only [monsterNortonOrderedPairIndex_eq_iff _ _ _ _
        (monsterNortonOctadThreeUOutputPair_lt e)
        (monsterNortonPairHalfUPoolOutputPair_lt _)]
    simp only [eq_comm]
    split_ifs <;> norm_num
  · simp only [hs, ht, ite_true, ite_false, false_and]
    rw [monsterNortonPairExtra_octad_form]
    norm_num
  · simp only [hs, ht, ite_false, ite_true]
    rw [monsterNortonOctadExtra_pair_form]
    norm_num
  · simp only [hs, ht, ite_false, ne_eq, not_false_eq_true, true_and]
    rw [monsterNortonOctadExtra_octad_form]
    simp only [eq_comm]
    split_ifs <;> norm_num

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
