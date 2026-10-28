/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingCandidateFinalTensorPacket00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingCandidateFinalTensorPacket01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingCandidateFinalTensorPacket02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingCandidateFinalTensorPacket03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingCandidateFinalTensorPacket04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingCandidateFinalTensorPacket05

/-! All complete normalized candidate final tensor columns retain their exact source formula. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

/-- Every original final tensor coordinate has the same retained exact normalized source input. -/
theorem generatedTwelfth_candidate_final_tensor_input : ∀ (n : Fin 4096) (j : Fin 24),
    generatedTwelfthCandidateFinalTensorInteger n j =
      2 * generatedTwelfthSpinTensorInputInteger n j := by
  intro n j
  fin_cases j
  · exact generatedTwelfth_candidate_final_tensor_column_00 n
  · exact generatedTwelfth_candidate_final_tensor_column_01 n
  · exact generatedTwelfth_candidate_final_tensor_column_02 n
  · exact generatedTwelfth_candidate_final_tensor_column_03 n
  · exact generatedTwelfth_candidate_final_tensor_column_04 n
  · exact generatedTwelfth_candidate_final_tensor_column_05 n
  · exact generatedTwelfth_candidate_final_tensor_column_06 n
  · exact generatedTwelfth_candidate_final_tensor_column_07 n
  · exact generatedTwelfth_candidate_final_tensor_column_08 n
  · exact generatedTwelfth_candidate_final_tensor_column_09 n
  · exact generatedTwelfth_candidate_final_tensor_column_10 n
  · exact generatedTwelfth_candidate_final_tensor_column_11 n
  · exact generatedTwelfth_candidate_final_tensor_column_12 n
  · exact generatedTwelfth_candidate_final_tensor_column_13 n
  · exact generatedTwelfth_candidate_final_tensor_column_14 n
  · exact generatedTwelfth_candidate_final_tensor_column_15 n
  · exact generatedTwelfth_candidate_final_tensor_column_16 n
  · exact generatedTwelfth_candidate_final_tensor_column_17 n
  · exact generatedTwelfth_candidate_final_tensor_column_18 n
  · exact generatedTwelfth_candidate_final_tensor_column_19 n
  · exact generatedTwelfth_candidate_final_tensor_column_20 n
  · exact generatedTwelfth_candidate_final_tensor_column_21 n
  · exact generatedTwelfth_candidate_final_tensor_column_22 n
  · exact generatedTwelfth_candidate_final_tensor_column_23 n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
