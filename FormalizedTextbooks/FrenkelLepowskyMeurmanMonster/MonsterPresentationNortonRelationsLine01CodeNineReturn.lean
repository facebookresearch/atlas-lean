/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Whole literal first-line square return on original preferred short basis fifteen. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeNineForwardBinding
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeNineInverseBinding
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeNineUTransport

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The square of the actual first-line difference fixes the entire fifteenth preferred vector. -/
theorem monsterNortonLineZeroOne_codeNine_return :
    ((y555NortonLine monsterSourceTriality 0 *
      (y555NortonLine monsterSourceTriality 1)⁻¹) ^ 2).val
        (monsterNortonPureShort (monsterNortonEvenShortBasis 15)) =
      monsterNortonPureShort (monsterNortonEvenShortBasis 15) := by
  apply monsterNortonLineZeroOne_square_return_of_packets _
    monsterNortonCodeNineForwardPacket monsterNortonCodeNineInversePacket
  · exact monsterNortonCodeNineForward_literal
  · exact monsterNortonCodeNineInverse_literal
  · rw [monsterNortonCodeNineU_transport]
    exact monsterNortonCodeNineInversePacket_norm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
