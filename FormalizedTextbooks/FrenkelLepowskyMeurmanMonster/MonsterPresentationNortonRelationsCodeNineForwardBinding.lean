/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The complete code-nine mixed candidate is the actual literal seven-operator forward packet. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeNineForwardPairings
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOrthonormalPacketIdentity

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- All actual supported reads and the actual whole norm identify the full code-nine packet. -/
theorem monsterNortonCodeNineForwardPacket_actual :
    monsterNortonMixedOddHalfPacket 3 = monsterNortonCodeNineForwardPacket := by
  unfold monsterNortonCodeNineForwardPacket
  apply monsterNortonOrthonormalPacket_identifies
  · exact monsterNortonMixedDictionary_gram _ _
      monsterNortonCodeNineForwardShortIndex_injective
      monsterNortonCodeNineForwardTensorIndex_injective
  · intro k
    rcases k with p | p
    · exact monsterNortonCodeNineForwardHalf_short_form p
    · exact monsterNortonCodeNineForwardHalf_tensor_form p
  · rw [monsterNortonMixedOddHalfPacket_norm]
    have h := monsterNortonCodeNineForwardPacket_norm
    unfold monsterNortonCodeNineForwardPacket at h
    rw [monsterNortonOrthonormalPacket_norm _ _
      (monsterNortonMixedDictionary_gram _ _
        monsterNortonCodeNineForwardShortIndex_injective
        monsterNortonCodeNineForwardTensorIndex_injective)] at h
    exact h.symm

/-- Seven actual word operators on original preferred basis fifteen give this full packet. -/
theorem monsterNortonCodeNineForward_literal :
    sExtra (y555NortonV.val ((y555NortonActualU⁻¹).val (y555NortonV.val (sExtra.symm
      (y555NortonActualU.val (y555NortonV.val
        (monsterNortonPureShort (monsterNortonEvenShortBasis 15)))))))) =
      monsterNortonCodeNineForwardPacket := by
  have h := monsterNortonMixedOddHalfPacket_actual 3
  rw [monsterNortonCodeNineForwardPacket_actual] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
