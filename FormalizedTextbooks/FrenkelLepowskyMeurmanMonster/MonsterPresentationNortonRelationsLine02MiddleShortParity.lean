/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Kernel checks of the complete original lattice parity in the middle short tables. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine02MiddleShortQData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 64000000 in
-- Check all 12288 genuine integer basis parity coordinates in the finite table.
/-- Every stored input parity agrees with the complete actual physical dictionary. -/
theorem monsterNortonLine02MiddleInputParity_actual (a : Fin 8) (e : Fin 64) (j : Fin 24) :
    integerParity (monsterNortonLeechCoordinates
      (monsterNortonLine02MiddleInputIntegral a e)) j =
      if (monsterNortonLine02MiddleInputParity a e).testBit j.val then 1 else 0 := by
  revert a e j
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 64000000 in
-- Check all 12288 genuine integer basis parity coordinates in the finite table.
/-- Every stored output parity agrees with the complete actual physical dictionary. -/
theorem monsterNortonLine02MiddleOutputParity_actual (a : Fin 8) (e : Fin 64) (j : Fin 24) :
    integerParity (monsterNortonLeechCoordinates
      (monsterNortonLine02MiddleOutputIntegral a e)) j =
      if (monsterNortonLine02MiddleOutputParity a e).testBit j.val then 1 else 0 := by
  revert a e j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
