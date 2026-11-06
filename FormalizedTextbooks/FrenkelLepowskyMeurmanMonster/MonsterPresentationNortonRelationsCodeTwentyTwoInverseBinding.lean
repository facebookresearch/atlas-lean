/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The complete code-twenty-two inverse candidate is the actual literal six-operator inverse
  packet. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyTwoInversePairings
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOrthonormalPacketIdentity

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- All actual supported reads and the whole actual norm identify the full inverse packet. -/
theorem monsterNortonCodeTwentyTwoInversePacket_actual :
    monsterNortonRemainingOctadInverseSixthPacket 9 = monsterNortonCodeTwentyTwoInversePacket := by
  unfold monsterNortonCodeTwentyTwoInversePacket
  apply monsterNortonOrthonormalPacket_identifies
  · exact monsterNortonMixedDictionary_gram _ _
      monsterNortonCodeTwentyTwoInverseShortIndex_injective
      monsterNortonCodeTwentyTwoInverseTensorIndex_injective
  · intro k
    rcases k with p | p
    · exact monsterNortonCodeTwentyTwoInverseHalf_short_form p
    · exact monsterNortonCodeTwentyTwoInverseHalf_tensor_form p
  · rw [monsterNortonRemainingOctadInverseSixthPacket_norm]
    have h := monsterNortonCodeTwentyTwoInversePacket_norm
    unfold monsterNortonCodeTwentyTwoInversePacket at h
    rw [monsterNortonOrthonormalPacket_norm _ _
      (monsterNortonMixedDictionary_gram _ _
        monsterNortonCodeTwentyTwoInverseShortIndex_injective
        monsterNortonCodeTwentyTwoInverseTensorIndex_injective)] at h
    exact h.symm

/-- Six actual operators on preferred basis22 give the complete inverse packet. -/
theorem monsterNortonCodeTwentyTwoInverse_literal :
    sExtra (y555NortonV.val (y555NortonActualU.val (y555NortonV.val (sExtra.symm
      (y555NortonV.val (monsterNortonPureShort (monsterNortonEvenShortBasis 22))))))) =
        monsterNortonCodeTwentyTwoInversePacket := by
  have h := monsterNortonRemainingOctadInverseBasis_actual 9
  rw [monsterNortonCodeTwentyTwoInversePacket_actual] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
