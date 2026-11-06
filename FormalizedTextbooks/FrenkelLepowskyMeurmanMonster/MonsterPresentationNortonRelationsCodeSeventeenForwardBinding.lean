/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete actual forward-half binding for original preferred short basis seventeen. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeSeventeenForwardPairings
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOrthonormalPacketIdentity

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Supported actual reads and the full actual norm identify the whole forward candidate. -/
theorem monsterNortonCodeSeventeenForwardPacket_actual :
    monsterNortonCodeSeventeenForwardActualPacket = monsterNortonCodeSeventeenForwardPacket := by
  unfold monsterNortonCodeSeventeenForwardPacket
  apply monsterNortonOrthonormalPacket_identifies
  · exact monsterNortonMixedDictionary_gram _ _
      monsterNortonCodeSeventeenForwardShortIndex_injective
      monsterNortonCodeSeventeenForwardTensorIndex_injective
  · intro k
    rcases k with p | p
    · exact monsterNortonCodeSeventeenForwardHalf_short_form p
    · exact monsterNortonCodeSeventeenForwardHalf_tensor_form p
  · rw [monsterNortonCodeSeventeenForwardActualPacket_norm]
    have h := monsterNortonCodeSeventeenForwardPacket_norm
    unfold monsterNortonCodeSeventeenForwardPacket at h
    rw [monsterNortonOrthonormalPacket_norm _ _
      (monsterNortonMixedDictionary_gram _ _
        monsterNortonCodeSeventeenForwardShortIndex_injective
        monsterNortonCodeSeventeenForwardTensorIndex_injective)] at h
    exact h.symm

/-- Seven original word operators on preferred basis seventeen give this full candidate. -/
theorem monsterNortonCodeSeventeenForward_literal :
    sExtra (y555NortonV.val ((y555NortonActualU⁻¹).val (y555NortonV.val (sExtra.symm
      (y555NortonActualU.val (y555NortonV.val
        (monsterNortonPureShort (monsterNortonEvenShortBasis 17)))))))) =
      monsterNortonCodeSeventeenForwardPacket := by
  rw [monsterNortonCodeSeventeenForwardActualPacket_actual,
    monsterNortonCodeSeventeenForwardPacket_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
