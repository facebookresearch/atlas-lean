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
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhBitsetCkpt3
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhBitsetCkpt4

/-! Stage 4 of the Seventh bitset forest: a single kernel computation of doubling steps
19 to 22 on natural-number bitsets of `2 ^ 24` positions. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Kernel check of doubling steps 19 to 22. -/
theorem seventhBitset_stage4 :
    tenthForestDoubles (seventhBitsetStageOps 3)
      seventhBitsetCheckpoint3 =
        seventhBitsetCheckpoint4 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
