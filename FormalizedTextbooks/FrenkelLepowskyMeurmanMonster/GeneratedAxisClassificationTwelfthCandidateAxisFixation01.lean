/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthAxisFixationOfCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCompleteShortPackedActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCompleteShortSupportPackedCertificates01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCandidateTensorCircuit01

/-! One complete actual full-axis fixer retains every original short and tensor equation. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- Genuine candidate 1 fixes the entire actual original candidate axis. -/
theorem generatedTwelfth_actual_candidate_axis_fix_01 :
    rhoLocal (generatedTwelfthCertifiedLocal 1) generatedTwelfthIncomingCandidateAxis =
      generatedTwelfthIncomingCandidateAxis := by
  apply generatedTwelfth_candidate_axis_fix_of_complete_certificates
  · intro a hnonzero
    exact generatedTwelfth_complete_short_condition_of_packed 1 a
      (generatedTwelfth_complete_short_support_packed_certificate_01 a hnonzero)
  · exact generatedTwelfth_candidate_tensor_circuit_01

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
