/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Whole literal first-line square return on original preferred short basis twenty. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyForwardBinding
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyInverseBinding
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyUTransport

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The square of the actual first-line difference fixes the entire twenty preferred vector. -/
theorem monsterNortonLineZeroOne_codeTwenty_return :
    ((y555NortonLine monsterSourceTriality 0 *
      (y555NortonLine monsterSourceTriality 1)⁻¹) ^ 2).val
        (monsterNortonPureShort (monsterNortonEvenShortBasis 20)) =
      monsterNortonPureShort (monsterNortonEvenShortBasis 20) := by
  apply monsterNortonLineZeroOne_square_return_of_packets _
    monsterNortonCodeTwentyForwardPacket monsterNortonCodeTwentyInversePacket
  · exact monsterNortonCodeTwentyForward_literal
  · exact monsterNortonCodeTwentyInverse_literal
  · rw [monsterNortonCodeTwentyU_transport]
    exact monsterNortonCodeTwentyInversePacket_norm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
