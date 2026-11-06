/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Whole literal first-line square return on original preferred short basis sixteen. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeSixteenForwardBinding
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeSixteenInverseBinding
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeSixteenUTransport

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The square of the actual first-line difference fixes the entire sixteenth preferred vector. -/
theorem monsterNortonLineZeroOne_codeSixteen_return :
    ((y555NortonLine monsterSourceTriality 0 *
      (y555NortonLine monsterSourceTriality 1)⁻¹) ^ 2).val
        (monsterNortonPureShort (monsterNortonEvenShortBasis 16)) =
      monsterNortonPureShort (monsterNortonEvenShortBasis 16) := by
  apply monsterNortonLineZeroOne_square_return_of_packets _
    monsterNortonCodeSixteenForwardPacket monsterNortonCodeSixteenInversePacket
  · exact monsterNortonCodeSixteenForward_literal
  · exact monsterNortonCodeSixteenInverse_literal
  · rw [monsterNortonCodeSixteenU_transport]
    exact monsterNortonCodeSixteenInversePacket_norm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
