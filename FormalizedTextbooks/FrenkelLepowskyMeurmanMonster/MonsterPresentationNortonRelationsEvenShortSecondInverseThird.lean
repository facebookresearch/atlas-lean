/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The first three actual inverse-half operators on the second preferred short basis input. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortFourth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsPairTrialityInverse
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairTwelfthV

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual physical pair underlying the second preferred basis unit. -/
noncomputable def monsterNortonEvenShortSecondPair : Fin 276 := griessPairIndex 0 2 (by decide)

/-- The second basis input is its original family-zero signed pair unit. -/
theorem monsterNortonEvenShortSecondPair_input :
    monsterNortonEvenShortBasis 1 = Sum.inl (0, monsterNortonEvenShortSecondPair) := by
  unfold monsterNortonEvenShortBasis monsterNortonEvenShortSecondPair
  rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Check both actual preferred-Q phases through the physical pair and source V binary dictionaries.
/-- V acts on the two genuine pair families with phases one and zero. -/
theorem monsterNortonEvenShortSecondPairVPhase (s : Fin 2) :
    monsterNortonVShortPhase (Sum.inl (s, monsterNortonEvenShortSecondPair)) =
      if s = 0 then 1 else 0 := by
  unfold monsterNortonVShortPhase
  rw [monsterNortonVBinaryCoordinates_actual]
  unfold monsterNortonShortQ
  simp only [griessShortIntegral, monsterNortonEvenShortSecondPair,
    griessPairIndex_coordinates]
  revert s
  decide +kernel

/-- Actual Q fixes every original A dictionary vector, for every physical pair. -/
theorem monsterNortonV_matrix_A (p : Fin 276) :
    y555NortonV.val (trialityABCBasis 0 p) = trialityABCBasis 0 p := by
  have h : trialityABCBasis 0 p = griessConwayDecode (trialityPairMatrix p, (0, 0)) := by
    rw [← griessConwayEncode_ABC_zero_sparse, griessConwayDecode_encode]
  rw [h, y555NortonV]
  exact monsterNortonQ_matrix_fixed y555NortonVQ _ (trialityPairMatrix_symmetric _)

/-- Actual V takes the entire second-pair B vector to minus its C vector. -/
theorem monsterNortonEvenShortSecondPairV_B :
    y555NortonV.val (trialityABCBasis 1 monsterNortonEvenShortSecondPair) =
      -trialityABCBasis 2 monsterNortonEvenShortSecondPair := by
  rw [monsterNortonPairShort_B, map_sub, monsterNortonV_pure_short,
    monsterNortonV_pure_short, monsterNortonEvenShortSecondPairVPhase,
    monsterNortonEvenShortSecondPairVPhase]
  simp only [ite_true, ite_eq_right (show (1 : Fin 2) ≠ 0 by decide),
    qSign_zero, qSign_one, neg_one_smul, one_smul]
  rw [monsterNortonPairShort_C]
  module

/-- The complete original-coordinate packet after the first three inverse-half operators. -/
noncomputable def monsterNortonEvenShortSecondInverseThirdPacket : GriessSpace :=
  (-1 / 2 : ℝ) • trialityABCBasis 0 monsterNortonEvenShortSecondPair +
    (1 / 2 : ℝ) • trialityABCBasis 2 monsterNortonEvenShortSecondPair

/-- The literal inverse-half V, inverse triality, V word has this entire actual vector image. -/
theorem monsterNortonEvenShortSecondInverseFirstThree_actual :
    y555NortonV.val (sExtra.symm (y555NortonV.val
      (monsterNortonPureShort (monsterNortonEvenShortBasis 1)))) =
        monsterNortonEvenShortSecondInverseThirdPacket := by
  rw [monsterNortonEvenShortSecondPair_input, monsterNortonV_pure_short,
    monsterNortonEvenShortSecondPairVPhase]
  simp only [ite_true, qSign_one, neg_one_smul]
  rw [map_neg, monsterNortonPairShort_extra_inverse, map_neg, map_add, map_smul, map_smul,
    monsterNortonEvenShortSecondPairV_B, monsterNortonV_matrix_A]
  simp only [ite_true]
  unfold monsterNortonEvenShortSecondInverseThirdPacket
  module

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
