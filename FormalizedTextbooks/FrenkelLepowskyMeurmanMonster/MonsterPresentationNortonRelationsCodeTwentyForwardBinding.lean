/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete actual forward-half binding for original preferred short basis twenty. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyForwardPairings
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOrthonormalPacketIdentity

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Supported actual reads and the full actual norm identify the whole forward candidate. -/
theorem monsterNortonCodeTwentyForwardPacket_actual :
    monsterNortonCodeTwentyForwardActualPacket = monsterNortonCodeTwentyForwardPacket := by
  unfold monsterNortonCodeTwentyForwardPacket
  apply monsterNortonOrthonormalPacket_identifies
  · exact monsterNortonMixedDictionary_gram _ _
      monsterNortonCodeTwentyForwardShortIndex_injective
      monsterNortonCodeTwentyForwardTensorIndex_injective
  · intro k
    rcases k with p | p
    · exact monsterNortonCodeTwentyForwardHalf_short_form p
    · exact monsterNortonCodeTwentyForwardHalf_tensor_form p
  · rw [monsterNortonCodeTwentyForwardActualPacket_norm]
    have h := monsterNortonCodeTwentyForwardPacket_norm
    unfold monsterNortonCodeTwentyForwardPacket at h
    rw [monsterNortonOrthonormalPacket_norm _ _
      (monsterNortonMixedDictionary_gram _ _
        monsterNortonCodeTwentyForwardShortIndex_injective
        monsterNortonCodeTwentyForwardTensorIndex_injective)] at h
    exact h.symm

/-- Seven original word operators on preferred basis twenty give this full candidate. -/
theorem monsterNortonCodeTwentyForward_literal :
    sExtra (y555NortonV.val ((y555NortonActualU⁻¹).val (y555NortonV.val (sExtra.symm
      (y555NortonActualU.val (y555NortonV.val
        (monsterNortonPureShort (monsterNortonEvenShortBasis 20)))))))) =
      monsterNortonCodeTwentyForwardPacket := by
  rw [monsterNortonCodeTwentyForwardActualPacket_actual,
    monsterNortonCodeTwentyForwardPacket_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
