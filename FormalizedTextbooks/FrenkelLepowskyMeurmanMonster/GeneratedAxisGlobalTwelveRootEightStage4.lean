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
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveRootEightCheckpoint3
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveRootEightCheckpoint4

/-! Stage 4 of the root-eight bitset forest: a single kernel computation of doubling
steps 18 to 22 on natural-number bitsets of `2 ^ 24` positions. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Kernel check of doubling steps 18 to 22. -/
theorem rootEightForest_stage4 :
    tenthForestDoubles (rootEightForestStageOps 3)
      rootEightForestCheckpoint3 = rootEightForestCheckpoint4 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
