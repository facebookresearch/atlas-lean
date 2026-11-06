/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The complete code-five inverse candidate is the actual literal six-operator inverse packet. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeFiveInversePairings
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOrthonormalPacketIdentity

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- All actual supported reads and the whole actual norm identify the full inverse packet. -/
theorem monsterNortonCodeFiveInversePacket_actual :
    monsterNortonRemainingOctadInverseSixthPacket 0 = monsterNortonCodeFiveInversePacket := by
  unfold monsterNortonCodeFiveInversePacket
  apply monsterNortonOrthonormalPacket_identifies
  · exact monsterNortonMixedDictionary_gram _ _
      monsterNortonCodeFiveInverseShortIndex_injective
      monsterNortonCodeFiveInverseTensorIndex_injective
  · intro k
    rcases k with p | p
    · exact monsterNortonCodeFiveInverseHalf_short_form p
    · exact monsterNortonCodeFiveInverseHalf_tensor_form p
  · rw [monsterNortonRemainingOctadInverseSixthPacket_norm]
    have h := monsterNortonCodeFiveInversePacket_norm
    unfold monsterNortonCodeFiveInversePacket at h
    rw [monsterNortonOrthonormalPacket_norm _ _
      (monsterNortonMixedDictionary_gram _ _
        monsterNortonCodeFiveInverseShortIndex_injective
        monsterNortonCodeFiveInverseTensorIndex_injective)] at h
    exact h.symm

/-- Six actual word operators on original preferred basis thirteen give the full inverse packet. -/
theorem monsterNortonCodeFiveInverse_literal :
    sExtra (y555NortonV.val (y555NortonActualU.val (y555NortonV.val (sExtra.symm
      (y555NortonV.val (monsterNortonPureShort (monsterNortonEvenShortBasis 13))))))) =
        monsterNortonCodeFiveInversePacket := by
  have h := monsterNortonRemainingOctadInverseBasis_actual 0
  rw [monsterNortonCodeFiveInversePacket_actual] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
