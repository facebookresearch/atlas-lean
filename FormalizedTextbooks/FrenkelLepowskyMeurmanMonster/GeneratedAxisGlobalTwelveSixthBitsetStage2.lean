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
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSixthBitsetCheckpoint2

/-! Stage 2 of the Sixth bitset forest: a single kernel computation of doubling steps
10 to 17 on natural-number bitsets of `2 ^ 24` positions. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Kernel check of doubling steps 10 to 17. -/
theorem sixthBitset_stage2 :
    tenthForestDoubles (sixthBitsetStageOps 1)
      sixthBitsetCheckpoint1 =
        sixthBitsetCheckpoint2 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
