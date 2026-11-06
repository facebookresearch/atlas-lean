/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete actual forward-half binding for original preferred short basis nineteen. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeNineteenForwardPairings
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOrthonormalPacketIdentity

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Supported actual reads and the full actual norm identify the whole forward candidate. -/
theorem monsterNortonCodeNineteenForwardPacket_actual :
    monsterNortonCodeNineteenForwardActualPacket = monsterNortonCodeNineteenForwardPacket := by
  unfold monsterNortonCodeNineteenForwardPacket
  apply monsterNortonOrthonormalPacket_identifies
  · exact monsterNortonMixedDictionary_gram _ _
      monsterNortonCodeNineteenForwardShortIndex_injective
      monsterNortonCodeNineteenForwardTensorIndex_injective
  · intro k
    rcases k with p | p
    · exact monsterNortonCodeNineteenForwardHalf_short_form p
    · exact monsterNortonCodeNineteenForwardHalf_tensor_form p
  · rw [monsterNortonCodeNineteenForwardActualPacket_norm]
    have h := monsterNortonCodeNineteenForwardPacket_norm
    unfold monsterNortonCodeNineteenForwardPacket at h
    rw [monsterNortonOrthonormalPacket_norm _ _
      (monsterNortonMixedDictionary_gram _ _
        monsterNortonCodeNineteenForwardShortIndex_injective
        monsterNortonCodeNineteenForwardTensorIndex_injective)] at h
    exact h.symm

/-- Seven original word operators on preferred basis nineteen give this full candidate. -/
theorem monsterNortonCodeNineteenForward_literal :
    sExtra (y555NortonV.val ((y555NortonActualU⁻¹).val (y555NortonV.val (sExtra.symm
      (y555NortonActualU.val (y555NortonV.val
        (monsterNortonPureShort (monsterNortonEvenShortBasis 19)))))))) =
      monsterNortonCodeNineteenForwardPacket := by
  rw [monsterNortonCodeNineteenForwardActualPacket_actual,
    monsterNortonCodeNineteenForwardPacket_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
