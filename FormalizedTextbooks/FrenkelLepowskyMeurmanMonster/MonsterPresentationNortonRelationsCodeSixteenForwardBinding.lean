/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete actual forward-half binding for original preferred short basis sixteen. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeSixteenForwardPairings
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOrthonormalPacketIdentity

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Supported actual reads and the full actual norm identify the whole forward candidate. -/
theorem monsterNortonCodeSixteenForwardPacket_actual :
    monsterNortonCodeSixteenForwardActualPacket = monsterNortonCodeSixteenForwardPacket := by
  unfold monsterNortonCodeSixteenForwardPacket
  apply monsterNortonOrthonormalPacket_identifies
  · exact monsterNortonMixedDictionary_gram _ _
      monsterNortonCodeSixteenForwardShortIndex_injective
      monsterNortonCodeSixteenForwardTensorIndex_injective
  · intro k
    rcases k with p | p
    · exact monsterNortonCodeSixteenForwardHalf_short_form p
    · exact monsterNortonCodeSixteenForwardHalf_tensor_form p
  · rw [monsterNortonCodeSixteenForwardActualPacket_norm]
    have h := monsterNortonCodeSixteenForwardPacket_norm
    unfold monsterNortonCodeSixteenForwardPacket at h
    rw [monsterNortonOrthonormalPacket_norm _ _
      (monsterNortonMixedDictionary_gram _ _
        monsterNortonCodeSixteenForwardShortIndex_injective
        monsterNortonCodeSixteenForwardTensorIndex_injective)] at h
    exact h.symm

/-- Seven original word operators on preferred basis sixteen give this full candidate. -/
theorem monsterNortonCodeSixteenForward_literal :
    sExtra (y555NortonV.val ((y555NortonActualU⁻¹).val (y555NortonV.val (sExtra.symm
      (y555NortonActualU.val (y555NortonV.val
        (monsterNortonPureShort (monsterNortonEvenShortBasis 16)))))))) =
      monsterNortonCodeSixteenForwardPacket := by
  rw [monsterNortonCodeSixteenForwardActualPacket_actual,
    monsterNortonCodeSixteenForwardPacket_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
