/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete actual forward-half binding for original preferred short basis eighteen. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeEighteenForwardPairings
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOrthonormalPacketIdentity

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Supported actual reads and the full actual norm identify the whole forward candidate. -/
theorem monsterNortonCodeEighteenForwardPacket_actual :
    monsterNortonCodeEighteenForwardActualPacket = monsterNortonCodeEighteenForwardPacket := by
  unfold monsterNortonCodeEighteenForwardPacket
  apply monsterNortonOrthonormalPacket_identifies
  · exact monsterNortonMixedDictionary_gram _ _
      monsterNortonCodeEighteenForwardShortIndex_injective
      monsterNortonCodeEighteenForwardTensorIndex_injective
  · intro k
    rcases k with p | p
    · exact monsterNortonCodeEighteenForwardHalf_short_form p
    · exact monsterNortonCodeEighteenForwardHalf_tensor_form p
  · rw [monsterNortonCodeEighteenForwardActualPacket_norm]
    have h := monsterNortonCodeEighteenForwardPacket_norm
    unfold monsterNortonCodeEighteenForwardPacket at h
    rw [monsterNortonOrthonormalPacket_norm _ _
      (monsterNortonMixedDictionary_gram _ _
        monsterNortonCodeEighteenForwardShortIndex_injective
        monsterNortonCodeEighteenForwardTensorIndex_injective)] at h
    exact h.symm

/-- Seven original word operators on preferred basis eighteen give this full candidate. -/
theorem monsterNortonCodeEighteenForward_literal :
    sExtra (y555NortonV.val ((y555NortonActualU⁻¹).val (y555NortonV.val (sExtra.symm
      (y555NortonActualU.val (y555NortonV.val
        (monsterNortonPureShort (monsterNortonEvenShortBasis 18)))))))) =
      monsterNortonCodeEighteenForwardPacket := by
  rw [monsterNortonCodeEighteenForwardActualPacket_actual,
    monsterNortonCodeEighteenForwardPacket_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
