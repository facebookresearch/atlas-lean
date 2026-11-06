/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthForestData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthForestCheckpoint4

/-! Stage 5 of the Tenth bitset forest: a single kernel computation of doubling steps
20 to 24 on natural-number bitsets of `2 ^ 24` positions. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Kernel check of doubling steps 20 to 24: every singular position is reached. -/
theorem tenthForest_stage5 :
    tenthForestNonsingular |||
      tenthForestDoubles (tenthForestStageOps 4) tenthForestCheckpoint4 = tenthForestAll := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
