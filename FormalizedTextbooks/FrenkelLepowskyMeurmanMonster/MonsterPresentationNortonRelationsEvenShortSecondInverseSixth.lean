/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete sixth actual inverse-half state on the second preferred short input. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortSecondInverseFifth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsMatrixTrialityCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortPositiveTriality

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The complete diagonal and pair-short packet contributed by the actual inverse-half matrix. -/
noncomputable def monsterNortonEvenShortSecondInverseSixthMatrix : GriessSpace :=
  griessConwayDecode
    (Matrix.diagonal (fun i => monsterNortonEvenShortSecondUMatrix i i),
      (monsterNortonMatrixTrialityShort monsterNortonEvenShortSecondUMatrix, 0))

/-- The entire sixth inverse-half packet retains both complete actual short Fourier images. -/
noncomputable def monsterNortonEvenShortSecondInverseSixthPacket : GriessSpace :=
  (-1 / 2 : ℝ) • monsterNortonEvenShortSecondInverseSixthMatrix +
    (-1 / 2 : ℝ) •
      (monsterNortonShortExtraPacket (monsterNortonEvenShortFirstUOutput 1) +
        monsterNortonShortExtraPacket monsterNortonEvenShortSecondUpperUShortOutput)

/-- Positive triality takes the whole fifth inverse-half vector to the stated sixth vector. -/
theorem monsterNortonEvenShortSecondInverseSixthPacket_actual :
    sExtra monsterNortonEvenShortSecondInverseFifthPacket =
      monsterNortonEvenShortSecondInverseSixthPacket := by
  rw [monsterNortonEvenShortSecondInverseFifthPacket, map_add, map_smul, map_smul,
    monsterNortonMatrix_extra_actual, map_add, monsterNortonShortExtraPacket_actual,
    monsterNortonShortExtraPacket_actual]
  rfl

/-- Six literal inverse-half operators give this complete original-coordinate second-basis image. -/
theorem monsterNortonEvenShortSecondInverseFirstSix_actual :
    sExtra (y555NortonV.val (y555NortonActualU.val (y555NortonV.val (sExtra.symm
      (y555NortonV.val (monsterNortonPureShort (monsterNortonEvenShortBasis 1))))))) =
        monsterNortonEvenShortSecondInverseSixthPacket := by
  rw [monsterNortonEvenShortSecondInverseFirstFive_actual,
    monsterNortonEvenShortSecondInverseSixthPacket_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
