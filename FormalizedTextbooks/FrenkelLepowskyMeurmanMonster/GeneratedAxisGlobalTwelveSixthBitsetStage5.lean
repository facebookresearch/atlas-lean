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
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSixthBitsetCheckpoint4

/-! Stage 5 of the Sixth bitset forest: a single kernel computation of doubling steps
30 to 33 on natural-number bitsets of `2 ^ 24` positions. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Kernel check of doubling steps 30 to 33: every singular position is reached. -/
theorem sixthBitset_stage5 :
    tenthForestNonsingular |||
      tenthForestDoubles (sixthBitsetStageOps 4)
        sixthBitsetCheckpoint4 = tenthForestAll := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
