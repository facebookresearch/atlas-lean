/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingCandidateFinalTensorData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinTensorInputData

/-! All original candidate final tensor coordinates in four complete physical columns. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
-- Verify every original spin label of this complete outgoing physical column.
/-- The candidate triality integer formula is twice the retained normalized final tensor input. -/
theorem generatedTwelfth_candidate_final_tensor_column_00 : ∀ n : Fin 4096,
    generatedTwelfthCandidateFinalTensorInteger n 0 =
      2 * generatedTwelfthSpinTensorInputInteger n 0 := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Verify every original spin label of this complete outgoing physical column.
/-- The candidate triality integer formula is twice the retained normalized final tensor input. -/
theorem generatedTwelfth_candidate_final_tensor_column_01 : ∀ n : Fin 4096,
    generatedTwelfthCandidateFinalTensorInteger n 1 =
      2 * generatedTwelfthSpinTensorInputInteger n 1 := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Verify every original spin label of this complete outgoing physical column.
/-- The candidate triality integer formula is twice the retained normalized final tensor input. -/
theorem generatedTwelfth_candidate_final_tensor_column_02 : ∀ n : Fin 4096,
    generatedTwelfthCandidateFinalTensorInteger n 2 =
      2 * generatedTwelfthSpinTensorInputInteger n 2 := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Verify every original spin label of this complete outgoing physical column.
/-- The candidate triality integer formula is twice the retained normalized final tensor input. -/
theorem generatedTwelfth_candidate_final_tensor_column_03 : ∀ n : Fin 4096,
    generatedTwelfthCandidateFinalTensorInteger n 3 =
      2 * generatedTwelfthSpinTensorInputInteger n 3 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
