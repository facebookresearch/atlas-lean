/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveRootEightForestSteps
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveRootEightCheckpoint2
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveRootEightCheckpoint3

/-! Stage 3 of the root-eight bitset forest: a single kernel computation of doubling
steps 13 to 17 on natural-number bitsets of `2 ^ 24` positions. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Kernel check of doubling steps 13 to 17. -/
theorem rootEightForest_stage3 :
    tenthForestDoubles (rootEightForestStageOps 2)
      rootEightForestCheckpoint2 = rootEightForestCheckpoint3 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
