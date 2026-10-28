/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The complete basis-ten inverse candidate is the actual literal six-operator inverse packet. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTenInversePairings
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOrthonormalPacketIdentity

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The actual complete sixth inverse word retains the norm of its original preferred unit. -/
theorem monsterNortonCodeTenInverse_source_norm :
    griessForm (monsterNortonEvenShortPairsInverseSixth 10 0)
      (monsterNortonEvenShortPairsInverseSixth 10 0) = 1 := by
  let x := monsterNortonPureShort (Sum.inl (0, monsterNortonEvenShortPairIndex 10))
  let g : G := extraIntoGenerated * y555NortonV * y555NortonActualU * y555NortonV *
    extraIntoGenerated⁻¹ * y555NortonV
  have h := generated_group_preserves_griessForm g x x
  change griessForm
    (sExtra (y555NortonV.val (y555NortonActualU.val (y555NortonV.val (sExtra.symm
      (y555NortonV.val x))))))
    (sExtra (y555NortonV.val (y555NortonActualU.val (y555NortonV.val (sExtra.symm
      (y555NortonV.val x)))))) = griessForm x x at h
  dsimp only [x] at h
  rw [monsterNortonEvenShortPairsInverseFirstSix_actual, monsterNortonPureShort_form] at h
  simpa only [ite_true] using h

/-- All actual supported reads and the whole actual norm identify the full inverse packet. -/
theorem monsterNortonCodeTenInversePacket_actual :
    monsterNortonEvenShortPairsInverseSixth 10 0 = monsterNortonCodeTenInversePacket := by
  unfold monsterNortonCodeTenInversePacket
  apply monsterNortonOrthonormalPacket_identifies
  · exact monsterNortonMixedDictionary_gram _ _
      monsterNortonCodeTenInverseShortIndex_injective
      monsterNortonCodeTenInverseTensorIndex_injective
  · intro k
    rcases k with p | p
    · exact monsterNortonCodeTenInverseHalf_short_form p
    · exact monsterNortonCodeTenInverseHalf_tensor_form p
  · rw [monsterNortonCodeTenInverse_source_norm]
    have h := monsterNortonCodeTenInversePacket_norm
    unfold monsterNortonCodeTenInversePacket at h
    rw [monsterNortonOrthonormalPacket_norm _ _
      (monsterNortonMixedDictionary_gram _ _
        monsterNortonCodeTenInverseShortIndex_injective
        monsterNortonCodeTenInverseTensorIndex_injective)] at h
    exact h.symm

/-- Six actual word operators on original preferred basis ten give the full inverse packet. -/
theorem monsterNortonCodeTenInverse_literal :
    sExtra (y555NortonV.val (y555NortonActualU.val (y555NortonV.val (sExtra.symm
      (y555NortonV.val (monsterNortonPureShort (monsterNortonEvenShortBasis 10))))))) =
        monsterNortonCodeTenInversePacket := by
  have h := monsterNortonEvenShortPairsInverseFirstSix_actual 10 0
  rw [← monsterNortonEvenShortPair_input 10] at h
  rw [monsterNortonCodeTenInversePacket_actual] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
