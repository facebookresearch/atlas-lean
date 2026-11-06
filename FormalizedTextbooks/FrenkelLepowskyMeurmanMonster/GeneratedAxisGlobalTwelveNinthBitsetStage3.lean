/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveNinthBitsetData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveNinthBitsetCheckpoint2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveNinthBitsetCheckpoint3

/-! Stage 3 of the Ninth bitset forest: a single kernel computation of doubling steps
11 to 15 on natural-number bitsets of `2 ^ 24` positions. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Kernel check of doubling steps 11 to 15. -/
theorem ninthForest_stage3 :
    tenthForestDoubles (ninthForestStageOps 2) ninthForestCheckpoint2 =
      ninthForestCheckpoint3 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
