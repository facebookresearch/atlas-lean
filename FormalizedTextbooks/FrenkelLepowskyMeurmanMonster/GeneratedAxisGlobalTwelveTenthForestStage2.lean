/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthForestData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthForestCheckpoint1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthForestCheckpoint2

/-! Stage 2 of the Tenth bitset forest: a single kernel computation of doubling steps
6 to 10 on natural-number bitsets of `2 ^ 24` positions. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Kernel check of doubling steps 6 to 10. -/
theorem tenthForest_stage2 :
    tenthForestDoubles (tenthForestStageOps 1) tenthForestCheckpoint1 = tenthForestCheckpoint2 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
