/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The complete code-seventeen inverse candidate is the actual literal six-operator inverse
  packet. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeSeventeenInversePairings
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOrthonormalPacketIdentity

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- All actual supported reads and the whole actual norm identify the full inverse packet. -/
theorem monsterNortonCodeSeventeenInversePacket_actual :
    monsterNortonRemainingOctadInverseSixthPacket 4 = monsterNortonCodeSeventeenInversePacket := by
  unfold monsterNortonCodeSeventeenInversePacket
  apply monsterNortonOrthonormalPacket_identifies
  · exact monsterNortonMixedDictionary_gram _ _
      monsterNortonCodeSeventeenInverseShortIndex_injective
      monsterNortonCodeSeventeenInverseTensorIndex_injective
  · intro k
    rcases k with p | p
    · exact monsterNortonCodeSeventeenInverseHalf_short_form p
    · exact monsterNortonCodeSeventeenInverseHalf_tensor_form p
  · rw [monsterNortonRemainingOctadInverseSixthPacket_norm]
    have h := monsterNortonCodeSeventeenInversePacket_norm
    unfold monsterNortonCodeSeventeenInversePacket at h
    rw [monsterNortonOrthonormalPacket_norm _ _
      (monsterNortonMixedDictionary_gram _ _
        monsterNortonCodeSeventeenInverseShortIndex_injective
        monsterNortonCodeSeventeenInverseTensorIndex_injective)] at h
    exact h.symm

/-- Six actual word operators on original preferred basis seventeen give the full inverse packet. -/
theorem monsterNortonCodeSeventeenInverse_literal :
    sExtra (y555NortonV.val (y555NortonActualU.val (y555NortonV.val (sExtra.symm
      (y555NortonV.val (monsterNortonPureShort (monsterNortonEvenShortBasis 17))))))) =
        monsterNortonCodeSeventeenInversePacket := by
  have h := monsterNortonRemainingOctadInverseBasis_actual 4
  rw [monsterNortonCodeSeventeenInversePacket_actual] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
