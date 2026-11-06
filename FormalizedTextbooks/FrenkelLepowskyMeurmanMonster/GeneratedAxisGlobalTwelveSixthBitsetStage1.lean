/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSixthBitsetData
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSixthBitsetCheckpoint1

/-! Stage 1 of the Sixth bitset forest: a single kernel computation of doubling steps
1 to 9 on natural-number bitsets of `2 ^ 24` positions. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Kernel check of doubling steps 1 to 9. -/
theorem sixthBitset_stage1 :
    tenthForestDoubles (sixthBitsetStageOps 0)
      sixthBitsetStart =
        sixthBitsetCheckpoint1 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
