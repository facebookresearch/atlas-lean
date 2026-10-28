/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Whole literal first-line square return on original preferred short basis ten. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTenForwardBinding
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTenInverseBinding
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTenUTransport

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The square of the actual first-line difference fixes the entire tenth preferred vector. -/
theorem monsterNortonLineZeroOne_codeTen_return :
    ((y555NortonLine monsterSourceTriality 0 *
      (y555NortonLine monsterSourceTriality 1)⁻¹) ^ 2).val
        (monsterNortonPureShort (monsterNortonEvenShortBasis 10)) =
      monsterNortonPureShort (monsterNortonEvenShortBasis 10) := by
  apply monsterNortonLineZeroOne_square_return_of_packets _
    monsterNortonCodeTenForwardPacket monsterNortonCodeTenInversePacket
  · exact monsterNortonCodeTenForward_literal
  · exact monsterNortonCodeTenInverse_literal
  · rw [monsterNortonCodeTenU_transport]
    exact monsterNortonCodeTenInversePacket_norm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
