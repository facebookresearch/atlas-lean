/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The complete code-nineteen inverse candidate is the actual literal six-operator inverse
  packet. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeNineteenInversePairings
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOrthonormalPacketIdentity

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- All actual supported reads and the whole actual norm identify the full inverse packet. -/
theorem monsterNortonCodeNineteenInversePacket_actual :
    monsterNortonRemainingOctadInverseSixthPacket 6 = monsterNortonCodeNineteenInversePacket := by
  unfold monsterNortonCodeNineteenInversePacket
  apply monsterNortonOrthonormalPacket_identifies
  · exact monsterNortonMixedDictionary_gram _ _
      monsterNortonCodeNineteenInverseShortIndex_injective
      monsterNortonCodeNineteenInverseTensorIndex_injective
  · intro k
    rcases k with p | p
    · exact monsterNortonCodeNineteenInverseHalf_short_form p
    · exact monsterNortonCodeNineteenInverseHalf_tensor_form p
  · rw [monsterNortonRemainingOctadInverseSixthPacket_norm]
    have h := monsterNortonCodeNineteenInversePacket_norm
    unfold monsterNortonCodeNineteenInversePacket at h
    rw [monsterNortonOrthonormalPacket_norm _ _
      (monsterNortonMixedDictionary_gram _ _
        monsterNortonCodeNineteenInverseShortIndex_injective
        monsterNortonCodeNineteenInverseTensorIndex_injective)] at h
    exact h.symm

/-- Six actual word operators on original preferred basis nineteen give the full inverse packet. -/
theorem monsterNortonCodeNineteenInverse_literal :
    sExtra (y555NortonV.val (y555NortonActualU.val (y555NortonV.val (sExtra.symm
      (y555NortonV.val (monsterNortonPureShort (monsterNortonEvenShortBasis 19))))))) =
        monsterNortonCodeNineteenInversePacket := by
  have h := monsterNortonRemainingOctadInverseBasis_actual 6
  rw [monsterNortonCodeNineteenInversePacket_actual] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
