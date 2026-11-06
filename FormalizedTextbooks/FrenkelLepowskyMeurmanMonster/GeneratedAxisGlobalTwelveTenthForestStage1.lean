/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthForestData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthForestCheckpoint1

/-! Stage 1 of the Tenth bitset forest: a single kernel computation of doubling steps
1 to 5 on natural-number bitsets of `2 ^ 24` positions. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Kernel check of doubling steps 1 to 5. -/
theorem tenthForest_stage1 :
    tenthForestDoubles (tenthForestStageOps 0) tenthForestStart = tenthForestCheckpoint1 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
