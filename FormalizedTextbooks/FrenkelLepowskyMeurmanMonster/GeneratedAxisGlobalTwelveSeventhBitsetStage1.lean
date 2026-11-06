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
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhBitsetCkpt1

/-! Stage 1 of the Seventh bitset forest: a single kernel computation of doubling steps
1 to 7 on natural-number bitsets of `2 ^ 24` positions. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Kernel check of doubling steps 1 to 7. -/
theorem seventhBitset_stage1 :
    tenthForestDoubles (seventhBitsetStageOps 0)
      seventhBitsetStart =
        seventhBitsetCheckpoint1 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
