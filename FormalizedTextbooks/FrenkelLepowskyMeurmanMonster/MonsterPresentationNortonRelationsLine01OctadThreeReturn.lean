/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Whole actual first-line square return on the original code-three octad unit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01ReturnFromPackets
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOctadThreeReturnPairing

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The literal first-line difference square fixes the entire twelfth basis octad unit. -/
theorem monsterNortonLineZeroOneSquare_octad_three_return :
    ((y555NortonLine monsterSourceTriality 0 *
      (y555NortonLine monsterSourceTriality 1)⁻¹) ^ 2).val
        (monsterNortonPureShort (monsterNortonEvenShortBasis 12)) =
      monsterNortonPureShort (monsterNortonEvenShortBasis 12) := by
  have hr : monsterNortonEvenShortBasis 12 = monsterNortonOctadThreeUInput 0 := rfl
  rw [hr]
  apply monsterNortonLineZeroOne_square_return_of_packets _
    (monsterNortonPairHalfPacket 11) monsterNortonOctadThreeInverseSixthPacket
  · simpa only [show monsterNortonPairHalfBasisIndex 11 = (12 : Fin 23) from rfl, hr] using
      monsterNortonEvenShortPairHalf_actual 11
  · exact monsterNortonOctadThreeInverseFirstSix_actual
  · exact monsterNortonOctadThreeReturnU_pairing_one

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
