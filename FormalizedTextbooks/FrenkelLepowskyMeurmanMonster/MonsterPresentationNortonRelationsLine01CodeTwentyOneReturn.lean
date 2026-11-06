/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Whole literal first-line square return on original preferred short basis twentyone. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyOneForwardBinding
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyOneInverseBinding
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyOneUTransport

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The square of the actual first-line difference fixes the entire twentyone preferred vector. -/
theorem monsterNortonLineZeroOne_codeTwentyOne_return :
    ((y555NortonLine monsterSourceTriality 0 *
      (y555NortonLine monsterSourceTriality 1)⁻¹) ^ 2).val
        (monsterNortonPureShort (monsterNortonEvenShortBasis 21)) =
      monsterNortonPureShort (monsterNortonEvenShortBasis 21) := by
  apply monsterNortonLineZeroOne_square_return_of_packets _
    monsterNortonCodeTwentyOneForwardPacket monsterNortonCodeTwentyOneInversePacket
  · exact monsterNortonCodeTwentyOneForward_literal
  · exact monsterNortonCodeTwentyOneInverse_literal
  · rw [monsterNortonCodeTwentyOneU_transport]
    exact monsterNortonCodeTwentyOneInversePacket_norm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
