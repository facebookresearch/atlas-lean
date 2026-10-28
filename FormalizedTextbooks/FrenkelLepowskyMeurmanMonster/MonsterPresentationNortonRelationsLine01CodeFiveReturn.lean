/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Whole literal first-line square return on original preferred short basis thirteen. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeFiveForwardBinding
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeFiveInverseBinding
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeFiveUTransport

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The square of the actual first-line difference fixes the entire thirteenth preferred vector. -/
theorem monsterNortonLineZeroOne_codeFive_return :
    ((y555NortonLine monsterSourceTriality 0 *
      (y555NortonLine monsterSourceTriality 1)⁻¹) ^ 2).val
        (monsterNortonPureShort (monsterNortonEvenShortBasis 13)) =
      monsterNortonPureShort (monsterNortonEvenShortBasis 13) := by
  apply monsterNortonLineZeroOne_square_return_of_packets _
    monsterNortonCodeFiveForwardPacket monsterNortonCodeFiveInversePacket
  · exact monsterNortonCodeFiveForward_literal
  · exact monsterNortonCodeFiveInverse_literal
  · rw [monsterNortonCodeFiveU_transport]
    exact monsterNortonCodeFiveInversePacket_norm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
