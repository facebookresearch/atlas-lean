/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsCoverageData

/-! Independent ordinary-kernel coverage certificate for first greedy label 15. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxHeartbeats 1000000000 in
-- One fixed first label bounds the finite prefix search independently.
set_option maxRecDepth 10000 in
-- The explicit Boolean finite search requires deeper ordinary reduction.
/-- All admissible four-vector extensions of this first label occur in the candidate table. -/
theorem generatedAxisE8FrameCandidateCoverage_label_015 :
    generatedAxisE8FrameCandidateCoverageAt 15 := by
  apply generatedAxisE8FrameCandidateCoverage_of_check
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
