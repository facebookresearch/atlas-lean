/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Whole literal first-line square return on original preferred short basis fourteen. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeSevenForwardBinding
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeSevenInverseBinding
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeSevenUTransport

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The square of the actual first-line difference fixes the entire fourteenth preferred vector. -/
theorem monsterNortonLineZeroOne_codeSeven_return :
    ((y555NortonLine monsterSourceTriality 0 *
      (y555NortonLine monsterSourceTriality 1)⁻¹) ^ 2).val
        (monsterNortonPureShort (monsterNortonEvenShortBasis 14)) =
      monsterNortonPureShort (monsterNortonEvenShortBasis 14) := by
  apply monsterNortonLineZeroOne_square_return_of_packets _
    monsterNortonCodeSevenForwardPacket monsterNortonCodeSevenInversePacket
  · exact monsterNortonCodeSevenForward_literal
  · exact monsterNortonCodeSevenInverse_literal
  · rw [monsterNortonCodeSevenU_transport]
    exact monsterNortonCodeSevenInversePacket_norm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
