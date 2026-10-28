/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Phase-complete actual first U images for the twenty-three preferred short basis units. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortFirstUData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairFirstU

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Check the complete actual central phase and all binary coordinates at twenty-three inputs.
/-- Each true U conjugation image is the preferred source lift, with its actual positive phase. -/
theorem monsterNortonEvenShortFirstU_Q_image (k : Fin 23) :
    spinConjugation monsterNortonUFiber.val.1
      (monsterNortonShortQ (monsterNortonEvenShortBasis k)) =
        monsterNortonShortQ (monsterNortonEvenShortFirstUOutput k) := by
  rw [monsterNortonUQImage_eq, monsterNortonUQFastImage_eq]
  unfold monsterNortonShortQ
  rw [monsterNortonEvenShortIntegral_actual, monsterNortonEvenShortFirstUIntegral_actual]
  apply NormalizedCocycleExtension.Extension.ext
  · funext i
    revert k i
    decide +kernel
  · revert k
    decide +kernel

/-- Literal U acts on each complete original short unit by the checked positive source image. -/
theorem monsterNortonEvenShortFirstU_actual (k : Fin 23) :
    y555NortonActualU.val (monsterNortonPureShort (monsterNortonEvenShortBasis k)) =
      monsterNortonPureShort (monsterNortonEvenShortFirstUOutput k) := by
  rw [← monsterNortonULocal_generated]
  change localGriessRepresentation monsterNortonUFiber
    (griessConwayDecode (0, (Pi.single (monsterNortonEvenShortBasis k) 1, 0))) =
      griessConwayDecode (0, (Pi.single (monsterNortonEvenShortFirstUOutput k) 1, 0))
  have h := monsterNortonGriessShortBasis_of_Q_image monsterNortonUFiber
    (monsterNortonEvenShortBasis k) (monsterNortonEvenShortFirstUOutput k) 0
    (by rw [show qCentral 0 = (1 : Q) from rfl, one_mul]
        exact monsterNortonEvenShortFirstU_Q_image k)
  simpa only [qSign_zero, one_smul] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
