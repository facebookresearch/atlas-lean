/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveEighthForestData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveEighthForestCheckpoint2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveEighthForestCheckpoint3

/-! Stage 3 of the Eighth bitset forest: a single kernel computation of doubling steps
11 to 15 on natural-number bitsets of `2 ^ 24` positions. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Kernel check of doubling steps 11 to 15. -/
theorem eighthForest_stage3 :
    tenthForestDoubles (eighthForestStageOps 2) eighthForestCheckpoint2 =
      eighthForestCheckpoint3 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
