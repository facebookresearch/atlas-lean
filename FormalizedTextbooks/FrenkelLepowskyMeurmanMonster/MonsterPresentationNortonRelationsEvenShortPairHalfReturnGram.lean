/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact actual form dictionary for the eleven complete preferred-pair return calculations. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortPairHalfReturnData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortPairHalfUPoolCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortPairsInversePairings
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsPairMatrixU

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every return case uses one of the ten original physical pairs with octad U outputs. -/
theorem monsterNortonPairReturnOriginal_lt (q : Fin 11) :
    (monsterNortonPairReturnOriginal q).val < 10 := by
  unfold monsterNortonPairReturnOriginal
  split_ifs <;> simp_all

/-- The integer base sign is precisely the true real V phase in the complete inverse packet. -/
theorem monsterNortonPairReturnBaseSign_actual (q : Fin 11) :
    qSign (monsterNortonEvenShortInitialVPhase
      ⟨(monsterNortonPairReturnOriginal q).val, by omega⟩) =
        (monsterNortonPairReturnBaseSign q : ℝ) := by
  rw [monsterNortonPairReturnBaseSign, nortonUIntegerSign_real]

/-- The integer family sign equals the actual original preferred pair-family sign. -/
theorem monsterNortonPairReturnFamilySign_actual (q : Fin 11) :
    monsterNortonPairFamilySign (monsterNortonPairReturnFamily q) =
      (monsterNortonPairReturnFamilySign q : ℝ) := by
  unfold monsterNortonPairReturnFamily monsterNortonPairReturnFamilySign
  split_ifs <;> norm_num [monsterNortonPairFamilySign]

/-- The source matrix numerator is the true physical U image used by the complete inverse packet. -/
theorem monsterNortonPairReturnSourceMatrix_actual (q : Fin 11) (i j : Fin 24) :
    monsterNortonEvenShortPairsUMatrix (monsterNortonPairReturnOriginal q) i j =
      (monsterNortonPairReturnSourceMatrixNumerator q i j : ℝ) / 16 := by
  rw [monsterNortonEvenShortPairsUMatrix, monsterNortonUPairMatrix_coordinates]
  simp only [monsterNortonUPairMatrixNumerator, monsterNortonEvenShortPairIndex,
    griessPairIndex_coordinates, monsterNortonEvenShortPairCoordinate_positive, ite_true,
    monsterNortonPairReturnSourceMatrixNumerator]

/-- The eight half-packet matrix numerators are their actual transported source A entries. -/
theorem monsterNortonPairReturnHalfMatrix_actual (q : Fin 11) (p : Fin 8) (i j : Fin 24) :
    conwayMatrixAction monsterNortonUFiber.val.2
      (trialityPairMatrix (monsterNortonPairHalfPairIndex (monsterNortonPairReturnCandidate q) p))
        i j = (monsterNortonPairReturnHalfMatrixNumerator q p i j : ℝ) / 16 := by
  rw [monsterNortonUPairMatrix_coordinates]
  simp only [monsterNortonUPairMatrixNumerator, monsterNortonPairHalfPairIndex,
    griessPairIndex_coordinates, monsterNortonPairHalfPair_lt, ite_true,
    monsterNortonPairReturnHalfMatrixNumerator]

/-- Every stored short Gram numerator is the whole actual inverse-packet form pairing. -/
theorem monsterNortonPairReturnInverseShortGram_actual (q : Fin 11)
    (i : NortonPairHalfShortIndex) :
    griessForm (monsterNortonEvenShortPairsInverseSixthNormalized
      (monsterNortonPairReturnOriginal q) (monsterNortonPairReturnFamily q))
      (monsterNortonPureShort (monsterNortonPairHalfUPoolOutput
        (monsterNortonPairHalfUPoolStorage (monsterNortonPairReturnCandidate q) i))) =
      (monsterNortonPairReturnInverseShortGram q i : ℝ) / 32 := by
  unfold monsterNortonPairHalfUPoolOutput monsterNortonPairReturnInverseShortGram
  by_cases hk : monsterNortonPairHalfUPoolOutputKind
      (monsterNortonPairHalfUPoolStorage (monsterNortonPairReturnCandidate q) i) = 0
  · simp only [hk, ite_true]
    rw [monsterNortonPairsInverseSixth_pair_form _ (monsterNortonPairReturnOriginal_lt q)]
    simp only [griessPairIndex_coordinates, monsterNortonPairHalfUPoolOutputPair_lt, ite_true]
    rw [monsterNortonPairReturnSourceMatrix_actual, monsterNortonPairReturnBaseSign_actual]
    split_ifs <;> push_cast <;> ring
  · simp only [hk, ite_false]
    rw [monsterNortonPairsInverseSixth_octad_form _ (monsterNortonPairReturnOriginal_lt q),
      monsterNortonPairReturnBaseSign_actual, monsterNortonPairReturnFamilySign_actual]
    simp_rw [monsterNortonOctadPositiveInteger_actual]
    split_ifs <;> push_cast <;> ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
