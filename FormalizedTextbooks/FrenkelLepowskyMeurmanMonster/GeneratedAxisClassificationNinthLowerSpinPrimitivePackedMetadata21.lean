/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinPrimitivePackedData

/-! Genuine full extraspecial primitive action, independent of full-word source certificates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

set_option maxHeartbeats 20000000 in
-- Check all24 full primitive unit images, all576 original cochain entries, and all central bits.
/-- This signed primitive's packed metadata is exactly its original full-Q cache. -/
theorem generatedNinth_lower_spin_primitive_packed_metadata_21 :
    generatedNinthLowerSpinPrimitivePackedMetadata 21 := by
  unfold generatedNinthLowerSpinPrimitivePackedMetadata
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
