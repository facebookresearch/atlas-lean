/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Bounded actual eleventh tensor factorization checks in original source coordinates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01EleventhSpinData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

set_option maxHeartbeats 16000000 in
-- Check both spin halves and six physical rows using the exact phase-corrected integer formula.
/-- Batch 2 of the exact actual eleventh tensor factorization coefficients. -/
theorem monsterNortonLine01EleventhTensor_coefficient_batch2
    (a : Fin 64) (h : Fin 2) (i : Fin 6) :
    monsterNortonLine01EleventhTensorIntegerNumerator
      ⟨(monsterNortonLine01ShortInputCode a).val + 2048 * h.val, by omega⟩
        ⟨12 + i.val, by omega⟩ =
          16 * monsterNortonLine01EleventhSpinVector
            ⟨(monsterNortonLine01ShortInputCode a).val + 2048 * h.val, by omega⟩ *
              monsterNortonUNumerator1 ⟨12 + i.val, by omega⟩ 0 := by
  revert a h i
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
