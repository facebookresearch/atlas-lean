/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The complete code-twentyone inverse candidate is the actual literal six-operator inverse
  packet. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyOneInversePairings
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOrthonormalPacketIdentity

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- All actual supported reads and the whole actual norm identify the full inverse packet. -/
theorem monsterNortonCodeTwentyOneInversePacket_actual :
    monsterNortonRemainingOctadInverseSixthPacket 8 = monsterNortonCodeTwentyOneInversePacket := by
  unfold monsterNortonCodeTwentyOneInversePacket
  apply monsterNortonOrthonormalPacket_identifies
  · exact monsterNortonMixedDictionary_gram _ _
      monsterNortonCodeTwentyOneInverseShortIndex_injective
      monsterNortonCodeTwentyOneInverseTensorIndex_injective
  · intro k
    rcases k with p | p
    · exact monsterNortonCodeTwentyOneInverseHalf_short_form p
    · exact monsterNortonCodeTwentyOneInverseHalf_tensor_form p
  · rw [monsterNortonRemainingOctadInverseSixthPacket_norm]
    have h := monsterNortonCodeTwentyOneInversePacket_norm
    unfold monsterNortonCodeTwentyOneInversePacket at h
    rw [monsterNortonOrthonormalPacket_norm _ _
      (monsterNortonMixedDictionary_gram _ _
        monsterNortonCodeTwentyOneInverseShortIndex_injective
        monsterNortonCodeTwentyOneInverseTensorIndex_injective)] at h
    exact h.symm

/-- Six actual word operators on original preferred basis twentyone give the full inverse packet. -/
theorem monsterNortonCodeTwentyOneInverse_literal :
    sExtra (y555NortonV.val (y555NortonActualU.val (y555NortonV.val (sExtra.symm
      (y555NortonV.val (monsterNortonPureShort (monsterNortonEvenShortBasis 21))))))) =
        monsterNortonCodeTwentyOneInversePacket := by
  have h := monsterNortonRemainingOctadInverseBasis_actual 8
  rw [monsterNortonCodeTwentyOneInversePacket_actual] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
