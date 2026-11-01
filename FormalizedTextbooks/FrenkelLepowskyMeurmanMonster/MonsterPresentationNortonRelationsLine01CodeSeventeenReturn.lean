/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Whole literal first-line square return on original preferred short basis seventeen. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeSeventeenForwardBinding
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeSeventeenInverseBinding
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeSeventeenUTransport

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The square of the actual first-line difference fixes the entire seventeen preferred vector. -/
theorem monsterNortonLineZeroOne_codeSeventeen_return :
    ((y555NortonLine monsterSourceTriality 0 *
      (y555NortonLine monsterSourceTriality 1)⁻¹) ^ 2).val
        (monsterNortonPureShort (monsterNortonEvenShortBasis 17)) =
      monsterNortonPureShort (monsterNortonEvenShortBasis 17) := by
  apply monsterNortonLineZeroOne_square_return_of_packets _
    monsterNortonCodeSeventeenForwardPacket monsterNortonCodeSeventeenInversePacket
  · exact monsterNortonCodeSeventeenForward_literal
  · exact monsterNortonCodeSeventeenInverse_literal
  · rw [monsterNortonCodeSeventeenU_transport]
    exact monsterNortonCodeSeventeenInversePacket_norm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
