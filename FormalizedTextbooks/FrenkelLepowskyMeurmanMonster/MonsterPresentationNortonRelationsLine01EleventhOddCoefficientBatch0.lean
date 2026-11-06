/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Bounded exact checks of the next actual inverse-triality odd-short coefficients. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01EleventhOddInteger

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

set_option maxHeartbeats 16000000 in
-- Check six physical rows against the exact sixteen-column tensor numerator.
/-- Batch 0 of the actual inverse-triality odd-short coefficients. -/
theorem monsterNortonLine01EleventhOdd_coefficient_batch0 (a : Fin 64) (i : Fin 6) :
    monsterNortonLine01EleventhOddIntegerNumerator (monsterNortonLine01ShortInputCode a)
      ⟨0 + i.val, by omega⟩ =
        if monsterNortonLine01ShortInputCode a = 82 ∧ (0 + i.val = 1) then 256 else 0 := by
  revert a i
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
