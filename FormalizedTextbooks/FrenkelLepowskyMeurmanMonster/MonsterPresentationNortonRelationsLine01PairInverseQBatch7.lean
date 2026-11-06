/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Checked actual inverse Norton images of octad packet entries 56 through 63. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairInverseShortInput

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
-- Check all binary coordinates and the full central phase through the genuine inverse cache.
/-- Eight entire Q images for the actual inverse-U octad packet, with no omitted phase. -/
theorem monsterNortonLine01PairInverseQ_batch7 (k : Fin 8) :
    monsterNortonUQInverseFastImage
      (monsterNortonShortQ (monsterNortonLine01PairInverseShortInput
        ⟨56 + k.val, by omega⟩)) =
          monsterNortonShortQ (monsterNortonLine01PairInverseShortOutput
            ⟨56 + k.val, by omega⟩) := by
  unfold monsterNortonShortQ
  rw [monsterNortonLine01PairInverseInputIntegral_actual,
    monsterNortonLine01PairInverseShortIntegral_actual]
  apply NormalizedCocycleExtension.Extension.ext
  · funext i
    revert i
    fin_cases k <;> decide +kernel
  · fin_cases k <;> decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
