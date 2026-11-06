/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsCoverageLabel019
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsCoverageLabel021
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsCoverageLabel022
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsCoverageLabel023
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsCoverageLabel025
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsCoverageLabel026
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsCoverageLabel027
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsCoverageLabel028
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsCoverageLabel029
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsCoverageLabel030
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsCoverageData

/-! Bounded ordinary-kernel coverage check for first greedy labels 16 through 31. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxHeartbeats 1000000000 in
-- One fixed first label keeps this finite kernel reduction bounded independently.
set_option maxRecDepth 10000 in
-- The nested finite label search requires deeper ordinary reduction.
private theorem generatedAxisE8FrameCandidateCoverage_label_016 :
    generatedAxisE8FrameCandidateCoverageAt 16 := by
  apply generatedAxisE8FrameCandidateCoverage_of_check
  decide +kernel

set_option maxHeartbeats 1000000000 in
-- One fixed first label keeps this finite kernel reduction bounded independently.
set_option maxRecDepth 10000 in
-- The nested finite label search requires deeper ordinary reduction.
private theorem generatedAxisE8FrameCandidateCoverage_label_017 :
    generatedAxisE8FrameCandidateCoverageAt 17 := by
  apply generatedAxisE8FrameCandidateCoverage_of_check
  decide +kernel

set_option maxHeartbeats 1000000000 in
-- One fixed first label keeps this finite kernel reduction bounded independently.
set_option maxRecDepth 10000 in
-- The nested finite label search requires deeper ordinary reduction.
private theorem generatedAxisE8FrameCandidateCoverage_label_018 :
    generatedAxisE8FrameCandidateCoverageAt 18 := by
  apply generatedAxisE8FrameCandidateCoverage_of_check
  decide +kernel

set_option maxHeartbeats 1000000000 in
-- One fixed first label keeps this finite kernel reduction bounded independently.
set_option maxRecDepth 10000 in
-- The nested finite label search requires deeper ordinary reduction.
private theorem generatedAxisE8FrameCandidateCoverage_label_020 :
    generatedAxisE8FrameCandidateCoverageAt 20 := by
  apply generatedAxisE8FrameCandidateCoverage_of_check
  decide +kernel

set_option maxHeartbeats 1000000000 in
-- One fixed first label keeps this finite kernel reduction bounded independently.
set_option maxRecDepth 10000 in
-- The nested finite label search requires deeper ordinary reduction.
private theorem generatedAxisE8FrameCandidateCoverage_label_024 :
    generatedAxisE8FrameCandidateCoverageAt 24 := by
  apply generatedAxisE8FrameCandidateCoverage_of_check
  decide +kernel

set_option maxHeartbeats 1000000000 in
-- One fixed first label keeps this finite kernel reduction bounded independently.
set_option maxRecDepth 10000 in
-- The nested finite label search requires deeper ordinary reduction.
private theorem generatedAxisE8FrameCandidateCoverage_label_031 :
    generatedAxisE8FrameCandidateCoverageAt 31 := by
  apply generatedAxisE8FrameCandidateCoverage_of_check
  decide +kernel

/-- Every admissible greedy basis in this first-label block has a displayed candidate tag. -/
theorem generatedAxisE8FrameCandidateCoverage_block_01 :
    ∀ i : Fin 16, generatedAxisE8FrameCandidateCoverageAt
      ⟨16 + i.val, by omega⟩ := by
  intro i
  fin_cases i
  · exact generatedAxisE8FrameCandidateCoverage_label_016
  · exact generatedAxisE8FrameCandidateCoverage_label_017
  · exact generatedAxisE8FrameCandidateCoverage_label_018
  · exact generatedAxisE8FrameCandidateCoverage_label_019
  · exact generatedAxisE8FrameCandidateCoverage_label_020
  · exact generatedAxisE8FrameCandidateCoverage_label_021
  · exact generatedAxisE8FrameCandidateCoverage_label_022
  · exact generatedAxisE8FrameCandidateCoverage_label_023
  · exact generatedAxisE8FrameCandidateCoverage_label_024
  · exact generatedAxisE8FrameCandidateCoverage_label_025
  · exact generatedAxisE8FrameCandidateCoverage_label_026
  · exact generatedAxisE8FrameCandidateCoverage_label_027
  · exact generatedAxisE8FrameCandidateCoverage_label_028
  · exact generatedAxisE8FrameCandidateCoverage_label_029
  · exact generatedAxisE8FrameCandidateCoverage_label_030
  · exact generatedAxisE8FrameCandidateCoverage_label_031

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
