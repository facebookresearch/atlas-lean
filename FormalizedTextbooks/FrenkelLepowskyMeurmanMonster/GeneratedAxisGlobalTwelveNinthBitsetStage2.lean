/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveNinthBitsetData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveNinthBitsetCheckpoint1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveNinthBitsetCheckpoint2

/-! Stage 2 of the Ninth bitset forest: a single kernel computation of doubling steps
6 to 10 on natural-number bitsets of `2 ^ 24` positions. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Kernel check of doubling steps 6 to 10. -/
theorem ninthForest_stage2 :
    tenthForestDoubles (ninthForestStageOps 1) ninthForestCheckpoint1 =
      ninthForestCheckpoint2 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
