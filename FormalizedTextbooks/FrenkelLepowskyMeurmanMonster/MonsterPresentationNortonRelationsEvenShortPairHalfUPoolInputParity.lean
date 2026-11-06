/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Original integral Leech parity certificates for all distinct actual sparse-packet inputs. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortPairHalfUPoolCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 128000000 in
-- Check all 37248 parity coordinates in the original integral Leech basis.
/-- Every cached input lattice parity coordinate agrees with its complete actual dictionary. -/
theorem monsterNortonPairHalfUPoolInputParity_actual (i : Fin 1552) (j : Fin 24) :
    integerParity (monsterNortonLeechCoordinates (monsterNortonPairHalfUPoolInputIntegral i)) j =
      if (monsterNortonPairHalfUPoolInputParity i).testBit j.val then 1 else 0 := by
  revert i j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
