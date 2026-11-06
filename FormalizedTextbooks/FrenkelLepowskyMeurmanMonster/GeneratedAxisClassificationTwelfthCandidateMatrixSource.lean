/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingCandidateBlocks

/-! Both complete triality outputs retain the same actual original matrix. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

set_option backward.isDefEq.respectTransparency false

/-- Equal incoming matrix and signed-short constituents give equal complete outgoing matrices. -/
theorem generatedTwelfth_candidate_original_matrix :
    (griessConwayEncode generatedTwelfthIncomingCandidateAxis).1 =
      (griessConwayEncode generatedTwelfthAxis).1 := by
  rw [generatedTwelfthAxis_local_expression]
  change (griessConwayEncode
    (sExtra (rhoLocal (localFiberIntoH generatedTwelfthIncomingCertifiedFiber)
      generatedFifthAxis))).1 = _
  rw [generatedAxisGlobalRawTrialityFormula_actual, generatedAxisGlobalRawTrialityFormula_actual]
  change generatedAxisGlobalRawTrialityMatrix
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedTwelfthIncomingCertifiedFiber)
      generatedFifthAxis)) = generatedAxisGlobalRawTrialityMatrix
    (griessConwayEncode (rhoLocal generatedTwelfthLocal generatedFifthAxis))
  have hb := generatedTwelfth_incoming_candidate_source_blocks
  rw [← generatedAxisGlobalFifthRoot09Packet_actual] at hb
  funext i j
  unfold generatedAxisGlobalRawTrialityMatrix
  rw [hb.1, hb.2, generatedTwelfthLocal]

/-- The entire actual candidate matrix equals the certified complete original matrix numerator. -/
theorem generatedTwelfth_candidate_matrix_actual :
    (griessConwayEncode generatedTwelfthIncomingCandidateAxis).1 =
      fun i j => (generatedTwelfthMatrixNumerator i j : ℝ) / 16 := by
  rw [generatedTwelfth_candidate_original_matrix, generatedTwelfth_matrix_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
