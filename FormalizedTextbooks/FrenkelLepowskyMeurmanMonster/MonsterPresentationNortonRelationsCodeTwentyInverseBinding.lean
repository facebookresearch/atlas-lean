/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The complete code-twenty inverse candidate is the actual literal six-operator inverse packet. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyInversePairings
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOrthonormalPacketIdentity

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- All actual supported reads and the whole actual norm identify the full inverse packet. -/
theorem monsterNortonCodeTwentyInversePacket_actual :
    monsterNortonRemainingOctadInverseSixthPacket 7 = monsterNortonCodeTwentyInversePacket := by
  unfold monsterNortonCodeTwentyInversePacket
  apply monsterNortonOrthonormalPacket_identifies
  · exact monsterNortonMixedDictionary_gram _ _
      monsterNortonCodeTwentyInverseShortIndex_injective
      monsterNortonCodeTwentyInverseTensorIndex_injective
  · intro k
    rcases k with p | p
    · exact monsterNortonCodeTwentyInverseHalf_short_form p
    · exact monsterNortonCodeTwentyInverseHalf_tensor_form p
  · rw [monsterNortonRemainingOctadInverseSixthPacket_norm]
    have h := monsterNortonCodeTwentyInversePacket_norm
    unfold monsterNortonCodeTwentyInversePacket at h
    rw [monsterNortonOrthonormalPacket_norm _ _
      (monsterNortonMixedDictionary_gram _ _
        monsterNortonCodeTwentyInverseShortIndex_injective
        monsterNortonCodeTwentyInverseTensorIndex_injective)] at h
    exact h.symm

/-- Six actual word operators on original preferred basis twenty give the full inverse packet. -/
theorem monsterNortonCodeTwentyInverse_literal :
    sExtra (y555NortonV.val (y555NortonActualU.val (y555NortonV.val (sExtra.symm
      (y555NortonV.val (monsterNortonPureShort (monsterNortonEvenShortBasis 20))))))) =
        monsterNortonCodeTwentyInversePacket := by
  have h := monsterNortonRemainingOctadInverseBasis_actual 7
  rw [monsterNortonCodeTwentyInversePacket_actual] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
