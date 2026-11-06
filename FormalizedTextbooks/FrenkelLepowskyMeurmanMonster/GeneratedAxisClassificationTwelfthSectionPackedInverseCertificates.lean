/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSectionPackedData

/-! Exact complete inverse binary matrices of the original eighteen section generators. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- Check all eighteen products on every entry of the complete twenty-four coordinate matrices.
/-- Every packed inverse is a genuine right inverse of the complete original binary matrix. -/
theorem generatedTwelfth_section_packed_inverse : ∀ g : Fin 18,
    sixthFrameOrbitColumnMatrix (generatedTwelfthSectionPackedForward g) *
      sixthFrameOrbitColumnMatrix (generatedTwelfthSectionPackedBackward g) = 1 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
