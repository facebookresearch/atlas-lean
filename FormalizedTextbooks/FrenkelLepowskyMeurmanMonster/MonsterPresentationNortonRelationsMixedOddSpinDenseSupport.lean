/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Supported coefficient agreement between the balanced dense and sparse candidate tables. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsMixedOddSpinDenseData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsMixedOddSpinTables

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

set_option maxHeartbeats 16000000 in
-- Check each of the 640 original supported entries against the full candidate table.
/-- Every listed support coefficient has its exact value in the complete coordinate table. -/
theorem monsterNortonMixedOddSpinDense_support (k : Fin 5) (i : Fin 128) :
    monsterNortonMixedOddSpinDense k (monsterNortonMixedOddSpinLabel k i) =
      monsterNortonMixedOddSpinCoefficient k i := by
  revert k i
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
