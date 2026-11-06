/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinTensorBoundedQuantifier

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCandidateCachedSourceFormulas
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinTensorInputData

/-! All original candidate final tensor coordinates in four complete physical columns. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
-- Verify every original spin label of this complete outgoing physical column.
/-- The candidate triality integer formula is twice the retained normalized final tensor input. -/
theorem generatedTwelfth_candidate_final_tensor_column_08 : ∀ n : Fin 4096,
    generatedTwelfthCandidateFinalTensorInteger n 8 =
      2 * generatedTwelfthSpinTensorInputInteger n 8 := by
  have hk : ∀ n : Fin 4096,
    generatedTwelfthCandidateFinalTensorCachedInteger n 8 =
      2 * generatedTwelfthSpinTensorInputInteger n 8 := by
    apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
    decide +kernel
  simpa only [generatedTwelfth_candidate_final_tensor_cached_actual] using hk

set_option maxHeartbeats 8000000 in
-- Verify every original spin label of this complete outgoing physical column.
/-- The candidate triality integer formula is twice the retained normalized final tensor input. -/
theorem generatedTwelfth_candidate_final_tensor_column_09 : ∀ n : Fin 4096,
    generatedTwelfthCandidateFinalTensorInteger n 9 =
      2 * generatedTwelfthSpinTensorInputInteger n 9 := by
  have hk : ∀ n : Fin 4096,
    generatedTwelfthCandidateFinalTensorCachedInteger n 9 =
      2 * generatedTwelfthSpinTensorInputInteger n 9 := by
    apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
    decide +kernel
  simpa only [generatedTwelfth_candidate_final_tensor_cached_actual] using hk

set_option maxHeartbeats 8000000 in
-- Verify every original spin label of this complete outgoing physical column.
/-- The candidate triality integer formula is twice the retained normalized final tensor input. -/
theorem generatedTwelfth_candidate_final_tensor_column_10 : ∀ n : Fin 4096,
    generatedTwelfthCandidateFinalTensorInteger n 10 =
      2 * generatedTwelfthSpinTensorInputInteger n 10 := by
  have hk : ∀ n : Fin 4096,
    generatedTwelfthCandidateFinalTensorCachedInteger n 10 =
      2 * generatedTwelfthSpinTensorInputInteger n 10 := by
    apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
    decide +kernel
  simpa only [generatedTwelfth_candidate_final_tensor_cached_actual] using hk

set_option maxHeartbeats 8000000 in
-- Verify every original spin label of this complete outgoing physical column.
/-- The candidate triality integer formula is twice the retained normalized final tensor input. -/
theorem generatedTwelfth_candidate_final_tensor_column_11 : ∀ n : Fin 4096,
    generatedTwelfthCandidateFinalTensorInteger n 11 =
      2 * generatedTwelfthSpinTensorInputInteger n 11 := by
  have hk : ∀ n : Fin 4096,
    generatedTwelfthCandidateFinalTensorCachedInteger n 11 =
      2 * generatedTwelfthSpinTensorInputInteger n 11 := by
    apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
    decide +kernel
  simpa only [generatedTwelfth_candidate_final_tensor_cached_actual] using hk

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
