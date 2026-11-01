/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSectionPackedData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SixthFrameOrbitMasks

/-! Complete packed binary coordinates retain the original eighteen source isometries. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
-- The kernel checks all entries of the complete original twenty-four coordinate matrix.
/-- Exact packed columns agree with the complete actual source binary action matrix. -/
theorem generatedTwelfth_section_packed_forward_4  :
    generatedTwelfthSectionBinaryMatrix 15 =
      sixthFrameOrbitColumnMatrix (generatedTwelfthSectionPackedForward 15) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
