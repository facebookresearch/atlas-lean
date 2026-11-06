/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Physical transport and full central phases give entire actual U images of the short pool. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortPairHalfUPoolPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortPairHalfUPoolPhysical
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortVectorQTransport

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Physical transport and the actual positive central phase identify the full preferred Q image. -/
theorem monsterNortonPairHalfUPool_Q_image (k : Fin 1552) :
    spinConjugation monsterNortonUFiber.val.1
      (monsterNortonShortQ (monsterNortonPairHalfUPoolInput k)) =
        monsterNortonShortQ (monsterNortonPairHalfUPoolOutput k) := by
  have hv := monsterNortonPairHalfUPoolPhysical_actual k
  have hh : monsterNortonUFiber.val.2.val
      (griessShortVector (monsterNortonPairHalfUPoolInput k)) =
      griessShortVector (monsterNortonPairHalfUPoolOutput k) ∨
      monsterNortonUFiber.val.2.val (griessShortVector (monsterNortonPairHalfUPoolInput k)) =
        -griessShortVector (monsterNortonPairHalfUPoolOutput k) := by
    rcases monsterNortonPairHalfUPoolPhysicalSign_unit k with hp | hn
    · left
      simpa only [hp, Int.cast_one, one_smul] using hv
    · right
      simpa only [hn, Int.cast_neg, Int.cast_one, neg_one_smul] using hv
  have h := monsterNortonShortQ_image_of_vector_phase monsterNortonUFiber
    (monsterNortonPairHalfUPoolInput k) (monsterNortonPairHalfUPoolOutput k) 0 hh
    (monsterNortonPairHalfUPoolPhase_actual k)
  simpa only [show qCentral 0 = (1 : Q) from rfl, one_mul] using h

/-- Literal actual U takes each entire opposite-family pair unit to its genuine source output. -/
theorem monsterNortonPairHalfUPool_actual (k : Fin 1552) :
    y555NortonActualU.val (monsterNortonPureShort (monsterNortonPairHalfUPoolInput k)) =
      monsterNortonPureShort (monsterNortonPairHalfUPoolOutput k) := by
  rw [← monsterNortonULocal_generated]
  change localGriessRepresentation monsterNortonUFiber
    (griessConwayDecode (0, (Pi.single (monsterNortonPairHalfUPoolInput k) 1, 0))) =
      griessConwayDecode (0, (Pi.single (monsterNortonPairHalfUPoolOutput k) 1, 0))
  have h := monsterNortonGriessShortBasis_of_Q_image monsterNortonUFiber
    (monsterNortonPairHalfUPoolInput k) (monsterNortonPairHalfUPoolOutput k) 0
    (by rw [show qCentral 0 = (1 : Q) from rfl, one_mul]
        exact monsterNortonPairHalfUPool_Q_image k)
  simpa only [qSign_zero, one_smul] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
