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
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveRootEightCheckpoint1
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveRootEightCheckpoint2

/-! Stage 2 of the root-eight bitset forest: a single kernel computation of doubling
steps 7 to 12 on natural-number bitsets of `2 ^ 24` positions. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Kernel check of doubling steps 7 to 12. -/
theorem rootEightForest_stage2 :
    tenthForestDoubles (rootEightForestStageOps 1)
      rootEightForestCheckpoint1 = rootEightForestCheckpoint2 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
