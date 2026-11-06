/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Whole actual U image of the opposite signed pair in the second preferred basis input. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortSecondUpperUData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortSecondInverseThird
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsPairMatrixU

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Check the actual full central phase and all binary coordinates through the certified U cache.
/-- The opposite genuine pair lift has the indicated preferred U image with central phase zero. -/
theorem monsterNortonEvenShortSecondUpperU_Q_image :
    spinConjugation monsterNortonUFiber.val.1
      (monsterNortonShortQ monsterNortonEvenShortSecondUpperShortInput) =
        monsterNortonShortQ monsterNortonEvenShortSecondUpperUShortOutput := by
  rw [monsterNortonUQImage_eq, monsterNortonUQFastImage_eq]
  unfold monsterNortonShortQ
  rw [monsterNortonEvenShortSecondUpperShortIntegral_actual,
    monsterNortonEvenShortSecondUpperUShortIntegral_actual]
  apply NormalizedCocycleExtension.Extension.ext
  · funext i
    revert i
    decide +kernel
  · decide +kernel

/-- Literal U sends the whole opposite short unit to its checked positive source octad unit. -/
theorem monsterNortonEvenShortSecondUpperU_actual :
    y555NortonActualU.val (monsterNortonPureShort monsterNortonEvenShortSecondUpperShortInput) =
      monsterNortonPureShort monsterNortonEvenShortSecondUpperUShortOutput := by
  rw [← monsterNortonULocal_generated]
  change localGriessRepresentation monsterNortonUFiber
    (griessConwayDecode (0, (Pi.single monsterNortonEvenShortSecondUpperShortInput 1, 0))) =
      griessConwayDecode (0, (Pi.single monsterNortonEvenShortSecondUpperUShortOutput 1, 0))
  have h := monsterNortonGriessShortBasis_of_Q_image monsterNortonUFiber
    monsterNortonEvenShortSecondUpperShortInput monsterNortonEvenShortSecondUpperUShortOutput 0
    (by rw [show qCentral 0 = (1 : Q) from rfl, one_mul]
        exact monsterNortonEvenShortSecondUpperU_Q_image)
  simpa only [qSign_zero, one_smul] using h

/-- The checked opposite pair is the actual family-one unit of the second physical pair. -/
theorem monsterNortonEvenShortSecondUpper_input :
    monsterNortonEvenShortSecondUpperShortInput =
      Sum.inl (1, monsterNortonEvenShortSecondPair) := by
  unfold monsterNortonEvenShortSecondUpperShortInput monsterNortonEvenShortSecondPair
  rfl

/-- U takes the whole second C vector to the sum of the two checked actual octad units. -/
theorem monsterNortonEvenShortSecondU_C :
    y555NortonActualU.val (trialityABCBasis 2 monsterNortonEvenShortSecondPair) =
      monsterNortonPureShort (monsterNortonEvenShortFirstUOutput 1) +
        monsterNortonPureShort monsterNortonEvenShortSecondUpperUShortOutput := by
  rw [monsterNortonPairShort_C, map_add, ← monsterNortonEvenShortSecondPair_input,
    ← monsterNortonEvenShortSecondUpper_input, monsterNortonEvenShortFirstU_actual,
    monsterNortonEvenShortSecondUpperU_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
