/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete actual Q and Griess short transport of the sparse second-input half packet. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortSecondHalfUPhysical
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortSecondHalfUPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortVectorQTransport

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The whole actual Q image agrees with its original preferred source output, including phase. -/
theorem monsterNortonSecondHalfU_Q_image (i : NortonSecondHalfShortIndex) :
    spinConjugation monsterNortonUFiber.val.1
      (monsterNortonShortQ (monsterNortonSecondHalfShortInput i)) =
        monsterNortonShortQ (monsterNortonSecondHalfShortUOutput i) := by
  have hv := monsterNortonSecondHalfUPhysical_actual i
  have h := monsterNortonShortQ_image_of_vector_phase monsterNortonUFiber
    (monsterNortonSecondHalfShortInput i) (monsterNortonSecondHalfShortUOutput i) 0
  have hh : monsterNortonUFiber.val.2.val
      (griessShortVector (monsterNortonSecondHalfShortInput i)) =
      griessShortVector (monsterNortonSecondHalfShortUOutput i) ∨
      monsterNortonUFiber.val.2.val (griessShortVector (monsterNortonSecondHalfShortInput i)) =
        -griessShortVector (monsterNortonSecondHalfShortUOutput i) := by
    rcases monsterNortonSecondHalfUPhysicalSign_unit i with hp | hn
    · left
      simpa only [hp, Int.cast_one, one_smul] using hv
    · right
      simpa only [hn, Int.cast_neg, Int.cast_one, neg_one_smul] using hv
  simpa only [show qCentral 0 = (1 : Q) from rfl, one_mul] using
    h hh (monsterNortonSecondHalfUPhase_actual i)

/-- Every actual sparse short input has the complete positive stated Griess image under U. -/
theorem monsterNortonSecondHalfU_short_actual (i : NortonSecondHalfShortIndex) :
    y555NortonActualU.val (monsterNortonPureShort (monsterNortonSecondHalfShortInput i)) =
      monsterNortonPureShort (monsterNortonSecondHalfShortUOutput i) := by
  rw [← monsterNortonULocal_generated]
  change localGriessRepresentation monsterNortonUFiber
    (griessConwayDecode (0, (Pi.single (monsterNortonSecondHalfShortInput i) 1, 0))) =
      griessConwayDecode (0, (Pi.single (monsterNortonSecondHalfShortUOutput i) 1, 0))
  have h := monsterNortonGriessShortBasis_of_Q_image monsterNortonUFiber
    (monsterNortonSecondHalfShortInput i) (monsterNortonSecondHalfShortUOutput i) 0
    (by rw [show qCentral 0 = (1 : Q) from rfl, one_mul]
        exact monsterNortonSecondHalfU_Q_image i)
  simpa only [qSign_zero, one_smul] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
