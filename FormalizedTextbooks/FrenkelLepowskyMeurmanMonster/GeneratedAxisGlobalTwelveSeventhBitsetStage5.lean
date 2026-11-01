/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhBitsetData
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhBitsetCkpt4

/-! Stage 5 of the Seventh bitset forest: a single kernel computation of doubling steps
23 to 25 on natural-number bitsets of `2 ^ 24` positions. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Kernel check of doubling steps 23 to 25: every singular position is reached. -/
theorem seventhBitset_stage5 :
    tenthForestNonsingular |||
      tenthForestDoubles (seventhBitsetStageOps 4)
        seventhBitsetCheckpoint4 = tenthForestAll := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
