/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Whole literal first-line square return on original preferred short basis twenty-two. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyTwoForwardBinding
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyTwoInverseBinding
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyTwoUTransport

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The square of the actual first-line difference fixes the entire twenty-second preferred
  vector. -/
theorem monsterNortonLineZeroOne_codeTwentyTwo_return :
    ((y555NortonLine monsterSourceTriality 0 *
      (y555NortonLine monsterSourceTriality 1)⁻¹) ^ 2).val
        (monsterNortonPureShort (monsterNortonEvenShortBasis 22)) =
      monsterNortonPureShort (monsterNortonEvenShortBasis 22) := by
  apply monsterNortonLineZeroOne_square_return_of_packets _
    monsterNortonCodeTwentyTwoForwardPacket monsterNortonCodeTwentyTwoInversePacket
  · exact monsterNortonCodeTwentyTwoForward_literal
  · exact monsterNortonCodeTwentyTwoInverse_literal
  · rw [monsterNortonCodeTwentyTwoU_transport]
    exact monsterNortonCodeTwentyTwoInversePacket_norm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
