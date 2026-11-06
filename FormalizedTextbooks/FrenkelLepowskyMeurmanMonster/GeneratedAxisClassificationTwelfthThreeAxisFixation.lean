/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthThreeLocalExact
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCandidateAxisFixation00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCandidateAxisFixation01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCandidateAxisFixation02

/-! Three independently completed genuine whole-axis fixers close the entire actual local count. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- All three required genuine compatible candidates fix the entire actual candidate axis. -/
theorem generatedTwelfth_three_candidate_axis_fixation :
    generatedTwelfthThreeCandidateAxisFixation := by
  intro g
  fin_cases g
  · exact generatedTwelfth_actual_candidate_axis_fix_00
  · exact generatedTwelfth_actual_candidate_axis_fix_01
  · exact generatedTwelfth_actual_candidate_axis_fix_02

/-- The full original local axis stabilizer has exactly 3,686,400 genuine group elements. -/
theorem generatedTwelfth_three_closed_actual_local_axis_stabilizer_card :
    Nat.card generatedTwelfthLocalAxisStabilizer = 3686400 :=
  generatedTwelfth_three_actual_local_axis_stabilizer_card
    generatedTwelfth_three_candidate_axis_fixation

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
