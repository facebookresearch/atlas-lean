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
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhBitsetCkpt2
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhBitsetCkpt3

/-! Stage 3 of the Seventh bitset forest: a single kernel computation of doubling steps
14 to 18 on natural-number bitsets of `2 ^ 24` positions. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Kernel check of doubling steps 14 to 18. -/
theorem seventhBitset_stage3 :
    tenthForestDoubles (seventhBitsetStageOps 2)
      seventhBitsetCheckpoint2 =
        seventhBitsetCheckpoint3 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
