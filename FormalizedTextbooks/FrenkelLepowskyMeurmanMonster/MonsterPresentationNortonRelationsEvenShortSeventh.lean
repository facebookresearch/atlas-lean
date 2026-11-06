/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete seventh literal line-word state on all twenty-three preferred short inputs. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortFifthSixth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortOddSeventh
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortPositiveTriality

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The whole seventh packet uses the exact tensor branch or phase-complete short dictionary. -/
noncomputable def monsterNortonEvenShortSeventhPacket (k : Fin 23) : GriessSpace :=
  if monsterNortonEvenShortFirstUIsOdd k then monsterNortonEvenShortOddSeventhPacket k else
    ∑ e : Fin 64, monsterNortonEvenShortSixthCoefficient k e •
      monsterNortonShortExtraPacket (monsterNortonEvenShortInverseUOutput k e)

/-- Positive triality transports each complete sixth vector to its stated seventh packet. -/
theorem monsterNortonEvenShortSeventhPacket_actual (k : Fin 23) :
    sExtra (monsterNortonEvenShortSixthPacket k) =
      monsterNortonEvenShortSeventhPacket k := by
  unfold monsterNortonEvenShortSixthPacket monsterNortonEvenShortSeventhPacket
  by_cases hk : monsterNortonEvenShortFirstUIsOdd k = true
  · simp only [ite_eq_left hk]
    exact monsterNortonEvenShortOddSeventhPacket_actual k
  · simp only [ite_eq_right hk]
    rw [map_sum]
    simp only [map_smul, monsterNortonShortExtraPacket_actual]

/-- Seven literal operators give this entire physical image on all twenty-three basis inputs. -/
theorem monsterNortonEvenShortFirstSeven_actual (k : Fin 23) :
    sExtra (y555NortonV.val ((y555NortonActualU⁻¹).val (y555NortonV.val (sExtra.symm
      (y555NortonActualU.val (y555NortonV.val
        (monsterNortonPureShort (monsterNortonEvenShortBasis k)))))))) =
      qSign (monsterNortonEvenShortInitialVPhase k) • monsterNortonEvenShortSeventhPacket k := by
  rw [monsterNortonEvenShortFirstSix_actual, map_smul,
    monsterNortonEvenShortSeventhPacket_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
