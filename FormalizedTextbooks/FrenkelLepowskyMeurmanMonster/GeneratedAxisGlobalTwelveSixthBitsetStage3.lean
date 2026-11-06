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
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSixthBitsetCheckpoint2
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSixthBitsetCheckpoint3

/-! Stage 3 of the Sixth bitset forest: a single kernel computation of doubling steps
18 to 25 on natural-number bitsets of `2 ^ 24` positions. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Kernel check of doubling steps 18 to 25. -/
theorem sixthBitset_stage3 :
    tenthForestDoubles (sixthBitsetStageOps 2)
      sixthBitsetCheckpoint2 =
        sixthBitsetCheckpoint3 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
