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
theorem generatedTwelfth_candidate_final_tensor_column_16 : ∀ n : Fin 4096,
    generatedTwelfthCandidateFinalTensorInteger n 16 =
      2 * generatedTwelfthSpinTensorInputInteger n 16 := by
  have hk : ∀ n : Fin 4096,
    generatedTwelfthCandidateFinalTensorCachedInteger n 16 =
      2 * generatedTwelfthSpinTensorInputInteger n 16 := by
    apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
    decide +kernel
  simpa only [generatedTwelfth_candidate_final_tensor_cached_actual] using hk

set_option maxHeartbeats 8000000 in
-- Verify every original spin label of this complete outgoing physical column.
/-- The candidate triality integer formula is twice the retained normalized final tensor input. -/
theorem generatedTwelfth_candidate_final_tensor_column_17 : ∀ n : Fin 4096,
    generatedTwelfthCandidateFinalTensorInteger n 17 =
      2 * generatedTwelfthSpinTensorInputInteger n 17 := by
  have hk : ∀ n : Fin 4096,
    generatedTwelfthCandidateFinalTensorCachedInteger n 17 =
      2 * generatedTwelfthSpinTensorInputInteger n 17 := by
    apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
    decide +kernel
  simpa only [generatedTwelfth_candidate_final_tensor_cached_actual] using hk

set_option maxHeartbeats 8000000 in
-- Verify every original spin label of this complete outgoing physical column.
/-- The candidate triality integer formula is twice the retained normalized final tensor input. -/
theorem generatedTwelfth_candidate_final_tensor_column_18 : ∀ n : Fin 4096,
    generatedTwelfthCandidateFinalTensorInteger n 18 =
      2 * generatedTwelfthSpinTensorInputInteger n 18 := by
  have hk : ∀ n : Fin 4096,
    generatedTwelfthCandidateFinalTensorCachedInteger n 18 =
      2 * generatedTwelfthSpinTensorInputInteger n 18 := by
    apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
    decide +kernel
  simpa only [generatedTwelfth_candidate_final_tensor_cached_actual] using hk

set_option maxHeartbeats 8000000 in
-- Verify every original spin label of this complete outgoing physical column.
/-- The candidate triality integer formula is twice the retained normalized final tensor input. -/
theorem generatedTwelfth_candidate_final_tensor_column_19 : ∀ n : Fin 4096,
    generatedTwelfthCandidateFinalTensorInteger n 19 =
      2 * generatedTwelfthSpinTensorInputInteger n 19 := by
  have hk : ∀ n : Fin 4096,
    generatedTwelfthCandidateFinalTensorCachedInteger n 19 =
      2 * generatedTwelfthSpinTensorInputInteger n 19 := by
    apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
    decide +kernel
  simpa only [generatedTwelfth_candidate_final_tensor_cached_actual] using hk

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
