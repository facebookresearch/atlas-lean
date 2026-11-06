/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveNinthBitsetData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveNinthBitsetCheckpoint3
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveNinthBitsetCheckpoint4

/-! Stage 4 of the Ninth bitset forest: a single kernel computation of doubling steps
16 to 20 on natural-number bitsets of `2 ^ 24` positions. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Kernel check of doubling steps 16 to 20. -/
theorem ninthForest_stage4 :
    tenthForestDoubles (ninthForestStageOps 3) ninthForestCheckpoint3 =
      ninthForestCheckpoint4 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
