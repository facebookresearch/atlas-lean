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

/-! Stage 1 of the root-eight bitset forest: a single kernel computation of doubling
steps 1 to 6 on natural-number bitsets of `2 ^ 24` positions. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Kernel check of doubling steps 1 to 6. -/
theorem rootEightForest_stage1 :
    tenthForestDoubles (rootEightForestStageOps 0)
      rootEightForestStart = rootEightForestCheckpoint1 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
