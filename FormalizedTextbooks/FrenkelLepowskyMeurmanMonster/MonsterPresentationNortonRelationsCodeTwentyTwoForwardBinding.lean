/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The complete basis22 mixed candidate is the actual literal seven-operator forward packet. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyTwoForwardPairings
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOrthonormalPacketIdentity

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- All actual supported reads and the actual whole norm identify the full basis22 packet. -/
theorem monsterNortonCodeTwentyTwoForwardPacket_actual :
    monsterNortonMixedOddHalfPacket 4 = monsterNortonCodeTwentyTwoForwardPacket := by
  unfold monsterNortonCodeTwentyTwoForwardPacket
  apply monsterNortonOrthonormalPacket_identifies
  · exact monsterNortonMixedDictionary_gram _ _
      monsterNortonCodeTwentyTwoForwardShortIndex_injective
      monsterNortonCodeTwentyTwoForwardTensorIndex_injective
  · intro k
    rcases k with p | p
    · exact monsterNortonCodeTwentyTwoForwardHalf_short_form p
    · exact monsterNortonCodeTwentyTwoForwardHalf_tensor_form p
  · rw [monsterNortonMixedOddHalfPacket_norm]
    have h := monsterNortonCodeTwentyTwoForwardPacket_norm
    unfold monsterNortonCodeTwentyTwoForwardPacket at h
    rw [monsterNortonOrthonormalPacket_norm _ _
      (monsterNortonMixedDictionary_gram _ _
        monsterNortonCodeTwentyTwoForwardShortIndex_injective
        monsterNortonCodeTwentyTwoForwardTensorIndex_injective)] at h
    exact h.symm

/-- Seven actual word operators on original preferred basis twenty-two give this full packet. -/
theorem monsterNortonCodeTwentyTwoForward_literal :
    sExtra (y555NortonV.val ((y555NortonActualU⁻¹).val (y555NortonV.val (sExtra.symm
      (y555NortonActualU.val (y555NortonV.val
        (monsterNortonPureShort (monsterNortonEvenShortBasis 22)))))))) =
      monsterNortonCodeTwentyTwoForwardPacket := by
  have h := monsterNortonMixedOddHalfPacket_actual 4
  rw [monsterNortonCodeTwentyTwoForwardPacket_actual] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
