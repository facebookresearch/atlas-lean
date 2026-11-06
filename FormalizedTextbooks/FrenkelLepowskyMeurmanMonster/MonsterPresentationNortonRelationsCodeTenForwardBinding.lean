/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The complete preferred-basis-ten mixed candidate is the actual literal seven-operator forward
packet. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTenForwardPairings
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOrthonormalPacketIdentity

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- All actual supported reads and the actual whole norm identify the full preferred-basis-ten
packet. -/
theorem monsterNortonCodeTenForwardPacket_actual :
    monsterNortonMixedOddHalfPacket 0 = monsterNortonCodeTenForwardPacket := by
  unfold monsterNortonCodeTenForwardPacket
  apply monsterNortonOrthonormalPacket_identifies
  · exact monsterNortonMixedDictionary_gram _ _
      monsterNortonCodeTenForwardShortIndex_injective
      monsterNortonCodeTenForwardTensorIndex_injective
  · intro k
    rcases k with p | p
    · exact monsterNortonCodeTenForwardHalf_short_form p
    · exact monsterNortonCodeTenForwardHalf_tensor_form p
  · rw [monsterNortonMixedOddHalfPacket_norm]
    have h := monsterNortonCodeTenForwardPacket_norm
    unfold monsterNortonCodeTenForwardPacket at h
    rw [monsterNortonOrthonormalPacket_norm _ _
      (monsterNortonMixedDictionary_gram _ _
        monsterNortonCodeTenForwardShortIndex_injective
        monsterNortonCodeTenForwardTensorIndex_injective)] at h
    exact h.symm

/-- Seven actual word operators on original preferred basis ten give this full packet. -/
theorem monsterNortonCodeTenForward_literal :
    sExtra (y555NortonV.val ((y555NortonActualU⁻¹).val (y555NortonV.val (sExtra.symm
      (y555NortonActualU.val (y555NortonV.val
        (monsterNortonPureShort (monsterNortonEvenShortBasis 10)))))))) =
      monsterNortonCodeTenForwardPacket := by
  have h := monsterNortonMixedOddHalfPacket_actual 0
  rw [monsterNortonCodeTenForwardPacket_actual] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
