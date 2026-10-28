/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Fully signed actual U images of eighth-step short inputs 120 through 149. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairEighthShortInput
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQImageCache

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Check every binary coordinate and the actual central coefficient through the true source U cache.
/-- Thirty entire actual U images, with their full signed original short-coordinate labels. -/
theorem monsterNortonLine01PairEighthQ_batch4 (k : Fin 30) :
    monsterNortonUQFastImage
      (monsterNortonShortQ (monsterNortonLine01PairEighthShortInput
        ⟨120 + k.val, by omega⟩)) =
          qCentral (monsterNortonLine01PairEighthPhase ⟨120 + k.val, by omega⟩) *
            monsterNortonShortQ (monsterNortonLine01PairEighthShortOutput
              ⟨120 + k.val, by omega⟩) := by
  unfold monsterNortonShortQ
  rw [monsterNortonLine01PairEighthInputIntegral_actual,
    monsterNortonLine01PairEighthOutputIntegral_actual]
  apply NormalizedCocycleExtension.Extension.ext
  · funext i
    revert i
    fin_cases k <;> decide +kernel
  · fin_cases k <;> decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
