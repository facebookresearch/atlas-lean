/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Whole literal first-line square return on original preferred short basis nineteen. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeNineteenForwardBinding
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeNineteenInverseBinding
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeNineteenUTransport

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The square of the actual first-line difference fixes the entire nineteen preferred vector. -/
theorem monsterNortonLineZeroOne_codeNineteen_return :
    ((y555NortonLine monsterSourceTriality 0 *
      (y555NortonLine monsterSourceTriality 1)⁻¹) ^ 2).val
        (monsterNortonPureShort (monsterNortonEvenShortBasis 19)) =
      monsterNortonPureShort (monsterNortonEvenShortBasis 19) := by
  apply monsterNortonLineZeroOne_square_return_of_packets _
    monsterNortonCodeNineteenForwardPacket monsterNortonCodeNineteenInversePacket
  · exact monsterNortonCodeNineteenForward_literal
  · exact monsterNortonCodeNineteenInverse_literal
  · rw [monsterNortonCodeNineteenU_transport]
    exact monsterNortonCodeNineteenInversePacket_norm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
