/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The complete code-nine inverse candidate is the actual literal six-operator inverse packet. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeNineInversePairings
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOrthonormalPacketIdentity

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- All actual supported reads and the whole actual norm identify the full inverse packet. -/
theorem monsterNortonCodeNineInversePacket_actual :
    monsterNortonRemainingOctadInverseSixthPacket 2 = monsterNortonCodeNineInversePacket := by
  unfold monsterNortonCodeNineInversePacket
  apply monsterNortonOrthonormalPacket_identifies
  · exact monsterNortonMixedDictionary_gram _ _
      monsterNortonCodeNineInverseShortIndex_injective
      monsterNortonCodeNineInverseTensorIndex_injective
  · intro k
    rcases k with p | p
    · exact monsterNortonCodeNineInverseHalf_short_form p
    · exact monsterNortonCodeNineInverseHalf_tensor_form p
  · rw [monsterNortonRemainingOctadInverseSixthPacket_norm]
    have h := monsterNortonCodeNineInversePacket_norm
    unfold monsterNortonCodeNineInversePacket at h
    rw [monsterNortonOrthonormalPacket_norm _ _
      (monsterNortonMixedDictionary_gram _ _
        monsterNortonCodeNineInverseShortIndex_injective
        monsterNortonCodeNineInverseTensorIndex_injective)] at h
    exact h.symm

/-- Six actual word operators on original preferred basis fifteen give the full inverse packet. -/
theorem monsterNortonCodeNineInverse_literal :
    sExtra (y555NortonV.val (y555NortonActualU.val (y555NortonV.val (sExtra.symm
      (y555NortonV.val (monsterNortonPureShort (monsterNortonEvenShortBasis 15))))))) =
        monsterNortonCodeNineInversePacket := by
  have h := monsterNortonRemainingOctadInverseBasis_actual 2
  rw [monsterNortonCodeNineInversePacket_actual] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
