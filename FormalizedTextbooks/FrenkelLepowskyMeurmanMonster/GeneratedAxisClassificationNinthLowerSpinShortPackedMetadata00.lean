/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinShortPackedData

/-! Exact full extraspecial action by finite bit masks. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

set_option maxHeartbeats 20000000 in
-- Check all twenty-four full source images, all 576 cocycle entries, and all central unit bits.
/-- The literal metadata is exactly the original full-Q corrected source generator data. -/
theorem generatedNinth_lower_spin_short_packed_metadata_00 :
    generatedNinthLowerSpinShortPackedMetadata 0 := by
  unfold generatedNinthLowerSpinShortPackedMetadata
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
