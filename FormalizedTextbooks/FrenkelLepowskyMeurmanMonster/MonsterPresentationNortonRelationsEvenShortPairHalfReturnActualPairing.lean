/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Maximal whole actual U-image pairings for eleven preferred-pair returns. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortPairHalfReturnPairing
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortPairHalfUWhole

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The whole actual U image has maximal pairing with the full normalized inverse-sixth packet. -/
theorem monsterNortonPairReturnU_pairing_one (q : Fin 11) :
    griessForm (y555NortonActualU.val
      (monsterNortonPairHalfPacket (monsterNortonPairReturnCandidate q)))
      (monsterNortonEvenShortPairsInverseSixthNormalized (monsterNortonPairReturnOriginal q)
        (monsterNortonPairReturnFamily q)) = 1 := by
  rw [monsterNortonPairHalfUWhole_actual, map_add, LinearMap.add_apply,
    monsterNortonPairReturnUMatrixPairing_actual, monsterNortonPairReturnUShortPairing_actual]
  norm_num

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
