/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual source coefficient equalities behind the finite second-half norm pairing. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortSecondHalfNormPairingData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortSecondInverseSixthPairings
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsPairMatrixU

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The displayed source matrix numerator is the actual U image used in the inverse-half packet. -/
theorem monsterNortonSecondSourceMatrixNumerator_actual (i j : Fin 24) :
    monsterNortonEvenShortSecondUMatrix i j =
      (monsterNortonSecondSourceMatrixNumerator i j : ℝ) / 16 := by
  rw [monsterNortonEvenShortSecondUMatrix, monsterNortonUPairMatrix_coordinates]
  simp only [monsterNortonUPairMatrixNumerator, monsterNortonEvenShortSecondPair,
    griessPairIndex_coordinates, show (0 : Fin 24) < 2 by decide, ite_true,
    monsterNortonSecondSourceMatrixNumerator]

/-- The finite half-packet matrix numerator is its actual transported physical A matrix entry. -/
theorem monsterNortonSecondHalfMatrixNumerator_actual (p : Fin 8) (i j : Fin 24) :
    conwayMatrixAction monsterNortonUFiber.val.2
      (trialityPairMatrix (monsterNortonSecondHalfPairIndex p)) i j =
        (monsterNortonSecondHalfMatrixNumerator p i j : ℝ) / 16 := by
  rw [monsterNortonUPairMatrix_coordinates]
  simp only [monsterNortonUPairMatrixNumerator, monsterNortonSecondHalfPairIndex,
    griessPairIndex_coordinates, monsterNortonSecondHalfPair_lt, ite_true,
    monsterNortonSecondHalfMatrixNumerator]

/-- Each reached short unit's displayed integer Gram value is its whole inverse-half pairing. -/
theorem monsterNortonSecondHalfInverseShortGram_actual (i : NortonSecondHalfShortIndex) :
    griessForm monsterNortonEvenShortSecondInverseSixthPacket
      (monsterNortonPureShort (monsterNortonSecondHalfShortUOutput i)) =
        (monsterNortonSecondHalfInverseShortGram i : ℝ) / 32 := by
  unfold monsterNortonSecondHalfShortUOutput monsterNortonSecondHalfInverseShortGram
  by_cases hk : monsterNortonSecondHalfUKind (monsterNortonSecondHalfShortStorage i) = 0
  · simp only [hk, ite_true]
    rw [monsterNortonSecondInverseSixth_pair_form]
    simp only [griessPairIndex_coordinates, monsterNortonSecondHalfUPair_lt, ite_true]
    rw [monsterNortonSecondSourceMatrixNumerator_actual]
    split_ifs <;> push_cast <;> ring
  · simp only [hk, ite_false]
    rw [monsterNortonSecondInverseSixth_octad_form]
    generalize hc : monsterNortonSecondHalfUOctadChoice (monsterNortonSecondHalfShortStorage i) = c
    fin_cases c <;>
      simp only [monsterNortonSecondHalfUOctadCode, Matrix.cons_val_zero,
        Fin.zero_eta, Fin.isValue] <;>
      norm_num <;> rw [monsterNortonOctadPositiveInteger_actual] <;> ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
