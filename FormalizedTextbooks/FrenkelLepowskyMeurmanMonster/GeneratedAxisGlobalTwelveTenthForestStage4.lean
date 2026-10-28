/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthForestData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthForestCheckpoint3
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthForestCheckpoint4

/-! Stage 4 of the Tenth bitset forest: a single kernel computation of doubling steps
16 to 19 on natural-number bitsets of `2 ^ 24` positions. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Kernel check of doubling steps 16 to 19. -/
theorem tenthForest_stage4 :
    tenthForestDoubles (tenthForestStageOps 3) tenthForestCheckpoint3 = tenthForestCheckpoint4 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
