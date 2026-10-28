/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsCoverageLabel007
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsCoverageLabel011
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsCoverageLabel013
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsCoverageLabel014
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsCoverageLabel015
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsCoverageData

/-! Bounded ordinary-kernel coverage check for first greedy labels 0 through 15. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxHeartbeats 1000000000 in
-- One fixed first label keeps this finite kernel reduction bounded independently.
set_option maxRecDepth 10000 in
-- The nested finite label search requires deeper ordinary reduction.
private theorem generatedAxisE8FrameCandidateCoverage_label_000 :
    generatedAxisE8FrameCandidateCoverageAt 0 := by
  apply generatedAxisE8FrameCandidateCoverage_of_check
  decide +kernel

set_option maxHeartbeats 1000000000 in
-- One fixed first label keeps this finite kernel reduction bounded independently.
set_option maxRecDepth 10000 in
-- The nested finite label search requires deeper ordinary reduction.
private theorem generatedAxisE8FrameCandidateCoverage_label_001 :
    generatedAxisE8FrameCandidateCoverageAt 1 := by
  apply generatedAxisE8FrameCandidateCoverage_of_check
  decide +kernel

set_option maxHeartbeats 1000000000 in
-- One fixed first label keeps this finite kernel reduction bounded independently.
set_option maxRecDepth 10000 in
-- The nested finite label search requires deeper ordinary reduction.
private theorem generatedAxisE8FrameCandidateCoverage_label_002 :
    generatedAxisE8FrameCandidateCoverageAt 2 := by
  apply generatedAxisE8FrameCandidateCoverage_of_check
  decide +kernel

set_option maxHeartbeats 1000000000 in
-- One fixed first label keeps this finite kernel reduction bounded independently.
set_option maxRecDepth 10000 in
-- The nested finite label search requires deeper ordinary reduction.
private theorem generatedAxisE8FrameCandidateCoverage_label_003 :
    generatedAxisE8FrameCandidateCoverageAt 3 := by
  apply generatedAxisE8FrameCandidateCoverage_of_check
  decide +kernel

set_option maxHeartbeats 1000000000 in
-- One fixed first label keeps this finite kernel reduction bounded independently.
set_option maxRecDepth 10000 in
-- The nested finite label search requires deeper ordinary reduction.
private theorem generatedAxisE8FrameCandidateCoverage_label_004 :
    generatedAxisE8FrameCandidateCoverageAt 4 := by
  apply generatedAxisE8FrameCandidateCoverage_of_check
  decide +kernel

set_option maxHeartbeats 1000000000 in
-- One fixed first label keeps this finite kernel reduction bounded independently.
set_option maxRecDepth 10000 in
-- The nested finite label search requires deeper ordinary reduction.
private theorem generatedAxisE8FrameCandidateCoverage_label_005 :
    generatedAxisE8FrameCandidateCoverageAt 5 := by
  apply generatedAxisE8FrameCandidateCoverage_of_check
  decide +kernel

set_option maxHeartbeats 1000000000 in
-- One fixed first label keeps this finite kernel reduction bounded independently.
set_option maxRecDepth 10000 in
-- The nested finite label search requires deeper ordinary reduction.
private theorem generatedAxisE8FrameCandidateCoverage_label_006 :
    generatedAxisE8FrameCandidateCoverageAt 6 := by
  apply generatedAxisE8FrameCandidateCoverage_of_check
  decide +kernel

set_option maxHeartbeats 1000000000 in
-- One fixed first label keeps this finite kernel reduction bounded independently.
set_option maxRecDepth 10000 in
-- The nested finite label search requires deeper ordinary reduction.
private theorem generatedAxisE8FrameCandidateCoverage_label_008 :
    generatedAxisE8FrameCandidateCoverageAt 8 := by
  apply generatedAxisE8FrameCandidateCoverage_of_check
  decide +kernel

set_option maxHeartbeats 1000000000 in
-- One fixed first label keeps this finite kernel reduction bounded independently.
set_option maxRecDepth 10000 in
-- The nested finite label search requires deeper ordinary reduction.
private theorem generatedAxisE8FrameCandidateCoverage_label_009 :
    generatedAxisE8FrameCandidateCoverageAt 9 := by
  apply generatedAxisE8FrameCandidateCoverage_of_check
  decide +kernel

set_option maxHeartbeats 1000000000 in
-- One fixed first label keeps this finite kernel reduction bounded independently.
set_option maxRecDepth 10000 in
-- The nested finite label search requires deeper ordinary reduction.
private theorem generatedAxisE8FrameCandidateCoverage_label_010 :
    generatedAxisE8FrameCandidateCoverageAt 10 := by
  apply generatedAxisE8FrameCandidateCoverage_of_check
  decide +kernel

set_option maxHeartbeats 1000000000 in
-- One fixed first label keeps this finite kernel reduction bounded independently.
set_option maxRecDepth 10000 in
-- The nested finite label search requires deeper ordinary reduction.
private theorem generatedAxisE8FrameCandidateCoverage_label_012 :
    generatedAxisE8FrameCandidateCoverageAt 12 := by
  apply generatedAxisE8FrameCandidateCoverage_of_check
  decide +kernel

/-- Every admissible greedy basis in this first-label block has a displayed candidate tag. -/
theorem generatedAxisE8FrameCandidateCoverage_block_00 :
    ∀ i : Fin 16, generatedAxisE8FrameCandidateCoverageAt
      ⟨0 + i.val, by omega⟩ := by
  intro i
  fin_cases i
  · exact generatedAxisE8FrameCandidateCoverage_label_000
  · exact generatedAxisE8FrameCandidateCoverage_label_001
  · exact generatedAxisE8FrameCandidateCoverage_label_002
  · exact generatedAxisE8FrameCandidateCoverage_label_003
  · exact generatedAxisE8FrameCandidateCoverage_label_004
  · exact generatedAxisE8FrameCandidateCoverage_label_005
  · exact generatedAxisE8FrameCandidateCoverage_label_006
  · exact generatedAxisE8FrameCandidateCoverage_label_007
  · exact generatedAxisE8FrameCandidateCoverage_label_008
  · exact generatedAxisE8FrameCandidateCoverage_label_009
  · exact generatedAxisE8FrameCandidateCoverage_label_010
  · exact generatedAxisE8FrameCandidateCoverage_label_011
  · exact generatedAxisE8FrameCandidateCoverage_label_012
  · exact generatedAxisE8FrameCandidateCoverage_label_013
  · exact generatedAxisE8FrameCandidateCoverage_label_014
  · exact generatedAxisE8FrameCandidateCoverage_label_015

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
