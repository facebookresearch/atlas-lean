/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The complete code-five mixed candidate is the actual literal seven-operator forward packet. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeFiveForwardPairings
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOrthonormalPacketIdentity

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- All actual supported reads and the actual whole norm identify the full code-five packet. -/
theorem monsterNortonCodeFiveForwardPacket_actual :
    monsterNortonMixedOddHalfPacket 1 = monsterNortonCodeFiveForwardPacket := by
  unfold monsterNortonCodeFiveForwardPacket
  apply monsterNortonOrthonormalPacket_identifies
  · exact monsterNortonMixedDictionary_gram _ _
      monsterNortonCodeFiveForwardShortIndex_injective
      monsterNortonCodeFiveForwardTensorIndex_injective
  · intro k
    rcases k with p | p
    · exact monsterNortonCodeFiveForwardHalf_short_form p
    · exact monsterNortonCodeFiveForwardHalf_tensor_form p
  · rw [monsterNortonMixedOddHalfPacket_norm]
    have h := monsterNortonCodeFiveForwardPacket_norm
    unfold monsterNortonCodeFiveForwardPacket at h
    rw [monsterNortonOrthonormalPacket_norm _ _
      (monsterNortonMixedDictionary_gram _ _
        monsterNortonCodeFiveForwardShortIndex_injective
        monsterNortonCodeFiveForwardTensorIndex_injective)] at h
    exact h.symm

/-- Seven actual word operators on original preferred basis thirteen give this full packet. -/
theorem monsterNortonCodeFiveForward_literal :
    sExtra (y555NortonV.val ((y555NortonActualU⁻¹).val (y555NortonV.val (sExtra.symm
      (y555NortonActualU.val (y555NortonV.val
        (monsterNortonPureShort (monsterNortonEvenShortBasis 13)))))))) =
      monsterNortonCodeFiveForwardPacket := by
  have h := monsterNortonMixedOddHalfPacket_actual 1
  rw [monsterNortonCodeFiveForwardPacket_actual] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
