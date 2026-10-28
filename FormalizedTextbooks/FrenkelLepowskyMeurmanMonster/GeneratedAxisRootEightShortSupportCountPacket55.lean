/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightShortSupportBlockCount

/-! Exact counts of both complete literal short supports in one original address interval. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

set_option maxHeartbeats 64000000 in
-- Count all1,024 original addresses, excluding only the24 unused final addresses.
/-- Both exact support counts retain every zero and every signed numerator in this complete block. -/
theorem generatedRootEight_short_support_count_packet_55 :
    generatedRootEightShortSupportBlockCount generatedRootEightPositiveFinalShortCachedNumerator 55 =
        0 ∧
      generatedRootEightShortSupportBlockCount generatedRootEightCanonicalShortCachedNumerator 55 =
        750 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
