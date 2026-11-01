/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The complete code-seven mixed candidate is the actual literal seven-operator forward packet. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeSevenForwardPairings
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOrthonormalPacketIdentity

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- All actual supported reads and the actual whole norm identify the full code-seven packet. -/
theorem monsterNortonCodeSevenForwardPacket_actual :
    monsterNortonMixedOddHalfPacket 2 = monsterNortonCodeSevenForwardPacket := by
  unfold monsterNortonCodeSevenForwardPacket
  apply monsterNortonOrthonormalPacket_identifies
  · exact monsterNortonMixedDictionary_gram _ _
      monsterNortonCodeSevenForwardShortIndex_injective
      monsterNortonCodeSevenForwardTensorIndex_injective
  · intro k
    rcases k with p | p
    · exact monsterNortonCodeSevenForwardHalf_short_form p
    · exact monsterNortonCodeSevenForwardHalf_tensor_form p
  · rw [monsterNortonMixedOddHalfPacket_norm]
    have h := monsterNortonCodeSevenForwardPacket_norm
    unfold monsterNortonCodeSevenForwardPacket at h
    rw [monsterNortonOrthonormalPacket_norm _ _
      (monsterNortonMixedDictionary_gram _ _
        monsterNortonCodeSevenForwardShortIndex_injective
        monsterNortonCodeSevenForwardTensorIndex_injective)] at h
    exact h.symm

/-- Seven actual word operators on original preferred basis fourteen give this full packet. -/
theorem monsterNortonCodeSevenForward_literal :
    sExtra (y555NortonV.val ((y555NortonActualU⁻¹).val (y555NortonV.val (sExtra.symm
      (y555NortonActualU.val (y555NortonV.val
        (monsterNortonPureShort (monsterNortonEvenShortBasis 14)))))))) =
      monsterNortonCodeSevenForwardPacket := by
  have h := monsterNortonMixedOddHalfPacket_actual 2
  rw [monsterNortonCodeSevenForwardPacket_actual] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
