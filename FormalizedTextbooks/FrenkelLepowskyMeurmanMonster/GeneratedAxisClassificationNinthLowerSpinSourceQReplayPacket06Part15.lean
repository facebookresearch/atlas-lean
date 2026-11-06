/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinPrimitivePackedReplayGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinLiteralQReplaySourcePacket06Part15
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinFastQMaskCentral

/-! Sixteen bounded chronological primitive steps, all full Q coordinate images. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_240 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 240 j := by
  change ∀ j : Fin 24, 240 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 240)
      (generatedNinthLowerSpinSourceQReplayWord 6 240 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 241 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_15 (0 : Fin 2)
  change generatedNinthLowerSpinSourceQReplayLetter 6 240 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part15.getD 0 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_15_240,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_15_241, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_241 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 241 j := by
  change ∀ j : Fin 24, 241 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 241)
      (generatedNinthLowerSpinSourceQReplayWord 6 241 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 242 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_15 (1 : Fin 2)
  change generatedNinthLowerSpinSourceQReplayLetter 6 241 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part15.getD 1 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_15_241,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_15_242, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

/-- Every actual primitive in this sixteen-step block retains all full central coordinates. -/
theorem generatedNinth_lower_spin_source_q_replay_packet_06_part_15 :
    ∀ n : Fin 16, ∀ j : Fin 24,
      240 + n.val < 242 →
        generatedNinthLowerSpinSourceQReplayStepCondition 6
          ⟨240 + n.val, by omega⟩ j := by
  intro n j hn
  fin_cases n
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_240 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_241 j)
  · norm_num at hn
  · norm_num at hn
  · norm_num at hn
  · norm_num at hn
  · norm_num at hn
  · norm_num at hn
  · norm_num at hn
  · norm_num at hn
  · norm_num at hn
  · norm_num at hn
  · norm_num at hn
  · norm_num at hn
  · norm_num at hn
  · norm_num at hn

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
