/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Whole literal first-line square return on original preferred short basis eighteen. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeEighteenForwardBinding
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeEighteenInverseBinding
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeEighteenUTransport

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The square of the actual first-line difference fixes the entire eighteen preferred vector. -/
theorem monsterNortonLineZeroOne_codeEighteen_return :
    ((y555NortonLine monsterSourceTriality 0 *
      (y555NortonLine monsterSourceTriality 1)⁻¹) ^ 2).val
        (monsterNortonPureShort (monsterNortonEvenShortBasis 18)) =
      monsterNortonPureShort (monsterNortonEvenShortBasis 18) := by
  apply monsterNortonLineZeroOne_square_return_of_packets _
    monsterNortonCodeEighteenForwardPacket monsterNortonCodeEighteenInversePacket
  · exact monsterNortonCodeEighteenForward_literal
  · exact monsterNortonCodeEighteenInverse_literal
  · rw [monsterNortonCodeEighteenU_transport]
    exact monsterNortonCodeEighteenInversePacket_norm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
