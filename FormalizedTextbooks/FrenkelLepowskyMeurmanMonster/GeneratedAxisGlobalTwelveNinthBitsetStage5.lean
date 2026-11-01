/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveNinthBitsetData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveNinthBitsetCheckpoint4

/-! Stage 5 of the Ninth bitset forest: a single kernel computation of doubling steps
21 to 26 on natural-number bitsets of `2 ^ 24` positions. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Kernel check of doubling steps 21 to 26: every singular position is reached. -/
theorem ninthForest_stage5 :
    tenthForestNonsingular |||
      tenthForestDoubles (ninthForestStageOps 4) ninthForestCheckpoint4 = tenthForestAll := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
