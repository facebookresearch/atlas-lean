/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete actual forward-half binding for original preferred short basis twentyone. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyOneForwardPairings
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOrthonormalPacketIdentity

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Supported actual reads and the full actual norm identify the whole forward candidate. -/
theorem monsterNortonCodeTwentyOneForwardPacket_actual :
    monsterNortonCodeTwentyOneForwardActualPacket = monsterNortonCodeTwentyOneForwardPacket := by
  unfold monsterNortonCodeTwentyOneForwardPacket
  apply monsterNortonOrthonormalPacket_identifies
  · exact monsterNortonMixedDictionary_gram _ _
      monsterNortonCodeTwentyOneForwardShortIndex_injective
      monsterNortonCodeTwentyOneForwardTensorIndex_injective
  · intro k
    rcases k with p | p
    · exact monsterNortonCodeTwentyOneForwardHalf_short_form p
    · exact monsterNortonCodeTwentyOneForwardHalf_tensor_form p
  · rw [monsterNortonCodeTwentyOneForwardActualPacket_norm]
    have h := monsterNortonCodeTwentyOneForwardPacket_norm
    unfold monsterNortonCodeTwentyOneForwardPacket at h
    rw [monsterNortonOrthonormalPacket_norm _ _
      (monsterNortonMixedDictionary_gram _ _
        monsterNortonCodeTwentyOneForwardShortIndex_injective
        monsterNortonCodeTwentyOneForwardTensorIndex_injective)] at h
    exact h.symm

/-- Seven original word operators on preferred basis twentyone give this full candidate. -/
theorem monsterNortonCodeTwentyOneForward_literal :
    sExtra (y555NortonV.val ((y555NortonActualU⁻¹).val (y555NortonV.val (sExtra.symm
      (y555NortonActualU.val (y555NortonV.val
        (monsterNortonPureShort (monsterNortonEvenShortBasis 21)))))))) =
      monsterNortonCodeTwentyOneForwardPacket := by
  rw [monsterNortonCodeTwentyOneForwardActualPacket_actual,
    monsterNortonCodeTwentyOneForwardPacket_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
