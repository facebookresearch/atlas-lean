/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveEighthForestData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveEighthForestCheckpoint1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveEighthForestCheckpoint2

/-! Stage 2 of the Eighth bitset forest: a single kernel computation of doubling steps
6 to 10 on natural-number bitsets of `2 ^ 24` positions. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Kernel check of doubling steps 6 to 10. -/
theorem eighthForest_stage2 :
    tenthForestDoubles (eighthForestStageOps 1) eighthForestCheckpoint1 =
      eighthForestCheckpoint2 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
