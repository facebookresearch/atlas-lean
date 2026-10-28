/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The complete code-sixteen inverse candidate is the actual literal six-operator inverse packet. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeSixteenInversePairings
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOrthonormalPacketIdentity

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- All actual supported reads and the whole actual norm identify the full inverse packet. -/
theorem monsterNortonCodeSixteenInversePacket_actual :
    monsterNortonRemainingOctadInverseSixthPacket 3 = monsterNortonCodeSixteenInversePacket := by
  unfold monsterNortonCodeSixteenInversePacket
  apply monsterNortonOrthonormalPacket_identifies
  · exact monsterNortonMixedDictionary_gram _ _
      monsterNortonCodeSixteenInverseShortIndex_injective
      monsterNortonCodeSixteenInverseTensorIndex_injective
  · intro k
    rcases k with p | p
    · exact monsterNortonCodeSixteenInverseHalf_short_form p
    · exact monsterNortonCodeSixteenInverseHalf_tensor_form p
  · rw [monsterNortonRemainingOctadInverseSixthPacket_norm]
    have h := monsterNortonCodeSixteenInversePacket_norm
    unfold monsterNortonCodeSixteenInversePacket at h
    rw [monsterNortonOrthonormalPacket_norm _ _
      (monsterNortonMixedDictionary_gram _ _
        monsterNortonCodeSixteenInverseShortIndex_injective
        monsterNortonCodeSixteenInverseTensorIndex_injective)] at h
    exact h.symm

/-- Six actual word operators on original preferred basis sixteen give the full inverse packet. -/
theorem monsterNortonCodeSixteenInverse_literal :
    sExtra (y555NortonV.val (y555NortonActualU.val (y555NortonV.val (sExtra.symm
      (y555NortonV.val (monsterNortonPureShort (monsterNortonEvenShortBasis 16))))))) =
        monsterNortonCodeSixteenInversePacket := by
  have h := monsterNortonRemainingOctadInverseBasis_actual 3
  rw [monsterNortonCodeSixteenInversePacket_actual] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
