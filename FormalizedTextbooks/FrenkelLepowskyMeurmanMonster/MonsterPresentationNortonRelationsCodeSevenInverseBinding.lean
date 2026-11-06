/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The complete code-seven inverse candidate is the actual literal six-operator inverse packet. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeSevenInversePairings
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOrthonormalPacketIdentity

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- All actual supported reads and the whole actual norm identify the full inverse packet. -/
theorem monsterNortonCodeSevenInversePacket_actual :
    monsterNortonRemainingOctadInverseSixthPacket 1 = monsterNortonCodeSevenInversePacket := by
  unfold monsterNortonCodeSevenInversePacket
  apply monsterNortonOrthonormalPacket_identifies
  · exact monsterNortonMixedDictionary_gram _ _
      monsterNortonCodeSevenInverseShortIndex_injective
      monsterNortonCodeSevenInverseTensorIndex_injective
  · intro k
    rcases k with p | p
    · exact monsterNortonCodeSevenInverseHalf_short_form p
    · exact monsterNortonCodeSevenInverseHalf_tensor_form p
  · rw [monsterNortonRemainingOctadInverseSixthPacket_norm]
    have h := monsterNortonCodeSevenInversePacket_norm
    unfold monsterNortonCodeSevenInversePacket at h
    rw [monsterNortonOrthonormalPacket_norm _ _
      (monsterNortonMixedDictionary_gram _ _
        monsterNortonCodeSevenInverseShortIndex_injective
        monsterNortonCodeSevenInverseTensorIndex_injective)] at h
    exact h.symm

/-- Six actual word operators on original preferred basis fourteen give the full inverse packet. -/
theorem monsterNortonCodeSevenInverse_literal :
    sExtra (y555NortonV.val (y555NortonActualU.val (y555NortonV.val (sExtra.symm
      (y555NortonV.val (monsterNortonPureShort (monsterNortonEvenShortBasis 14))))))) =
        monsterNortonCodeSevenInversePacket := by
  have h := monsterNortonRemainingOctadInverseBasis_actual 1
  rw [monsterNortonCodeSevenInversePacket_actual] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
