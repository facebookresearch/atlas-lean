/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Full actual integer basis parity of every middle squared-U pool input and output. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine02MiddleUPoolCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 256000000 in
-- Check all 30336 actual integer basis parity coordinates of this finite dictionary.
/-- Every packed input parity is the complete original physical lattice parity. -/
theorem monsterNortonLine02MiddleUPoolInputParity_actual (i : Fin 1264) (j : Fin 24) :
    integerParity (monsterNortonLeechCoordinates
      (monsterNortonLine02MiddleUPoolInputIntegral i)) j =
      if (monsterNortonLine02MiddleUPoolInputParity i).testBit j.val then 1 else 0 := by
  revert i j
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 256000000 in
-- Check all 30336 actual integer basis parity coordinates of this finite dictionary.
/-- Every packed output parity is the complete original physical lattice parity. -/
theorem monsterNortonLine02MiddleUPoolOutputParity_actual (i : Fin 1264) (j : Fin 24) :
    integerParity (monsterNortonLeechCoordinates
      (monsterNortonLine02MiddleUPoolOutputIntegral i)) j =
      if (monsterNortonLine02MiddleUPoolOutputParity i).testBit j.val then 1 else 0 := by
  revert i j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
