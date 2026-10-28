/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinPrimitivePackedReplayGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinLiteralQReplaySourcePacket06Part08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinFastQMaskCentral

/-! Sixteen bounded chronological primitive steps, all full Q coordinate images. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_128 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 128 j := by
  change ∀ j : Fin 24, 128 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 128)
      (generatedNinthLowerSpinSourceQReplayWord 6 128 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 129 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_08 (0 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 128 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part08.getD 0 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_08_128,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_08_129, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_129 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 129 j := by
  change ∀ j : Fin 24, 129 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 129)
      (generatedNinthLowerSpinSourceQReplayWord 6 129 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 130 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_08 (1 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 129 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part08.getD 1 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_08_129,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_08_130, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_130 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 130 j := by
  change ∀ j : Fin 24, 130 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 130)
      (generatedNinthLowerSpinSourceQReplayWord 6 130 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 131 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_08 (2 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 130 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part08.getD 2 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_08_130,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_08_131, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_131 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 131 j := by
  change ∀ j : Fin 24, 131 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 131)
      (generatedNinthLowerSpinSourceQReplayWord 6 131 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 132 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_08 (3 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 131 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part08.getD 3 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_08_131,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_08_132, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_132 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 132 j := by
  change ∀ j : Fin 24, 132 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 132)
      (generatedNinthLowerSpinSourceQReplayWord 6 132 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 133 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_08 (4 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 132 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part08.getD 4 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_08_132,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_08_133, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_133 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 133 j := by
  change ∀ j : Fin 24, 133 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 133)
      (generatedNinthLowerSpinSourceQReplayWord 6 133 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 134 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_08 (5 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 133 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part08.getD 5 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_08_133,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_08_134, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_134 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 134 j := by
  change ∀ j : Fin 24, 134 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 134)
      (generatedNinthLowerSpinSourceQReplayWord 6 134 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 135 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_08 (6 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 134 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part08.getD 6 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_08_134,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_08_135, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_135 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 135 j := by
  change ∀ j : Fin 24, 135 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 135)
      (generatedNinthLowerSpinSourceQReplayWord 6 135 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 136 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_08 (7 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 135 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part08.getD 7 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_08_135,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_08_136, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_136 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 136 j := by
  change ∀ j : Fin 24, 136 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 136)
      (generatedNinthLowerSpinSourceQReplayWord 6 136 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 137 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_08 (8 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 136 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part08.getD 8 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_08_136,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_08_137, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_137 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 137 j := by
  change ∀ j : Fin 24, 137 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 137)
      (generatedNinthLowerSpinSourceQReplayWord 6 137 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 138 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_08 (9 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 137 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part08.getD 9 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_08_137,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_08_138, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_138 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 138 j := by
  change ∀ j : Fin 24, 138 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 138)
      (generatedNinthLowerSpinSourceQReplayWord 6 138 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 139 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_08 (10 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 138 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part08.getD 10 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_08_138,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_08_139, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_139 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 139 j := by
  change ∀ j : Fin 24, 139 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 139)
      (generatedNinthLowerSpinSourceQReplayWord 6 139 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 140 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_08 (11 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 139 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part08.getD 11 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_08_139,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_08_140, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_140 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 140 j := by
  change ∀ j : Fin 24, 140 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 140)
      (generatedNinthLowerSpinSourceQReplayWord 6 140 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 141 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_08 (12 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 140 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part08.getD 12 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_08_140,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_08_141, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_141 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 141 j := by
  change ∀ j : Fin 24, 141 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 141)
      (generatedNinthLowerSpinSourceQReplayWord 6 141 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 142 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_08 (13 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 141 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part08.getD 13 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_08_141,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_08_142, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_142 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 142 j := by
  change ∀ j : Fin 24, 142 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 142)
      (generatedNinthLowerSpinSourceQReplayWord 6 142 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 143 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_08 (14 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 142 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part08.getD 14 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_08_142,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_08_143, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_143 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 143 j := by
  change ∀ j : Fin 24, 143 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 143)
      (generatedNinthLowerSpinSourceQReplayWord 6 143 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 144 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_08 (15 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 143 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part08.getD 15 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_08_143,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_08_144, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

/-- Every actual primitive in this sixteen-step block retains all full central coordinates. -/
theorem generatedNinth_lower_spin_source_q_replay_packet_06_part_08 :
    ∀ n : Fin 16, ∀ j : Fin 24,
      128 + n.val < 242 →
        generatedNinthLowerSpinSourceQReplayStepCondition 6
          ⟨128 + n.val, by omega⟩ j := by
  intro n j hn
  fin_cases n
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_128 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_129 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_130 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_131 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_132 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_133 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_134 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_135 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_136 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_137 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_138 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_139 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_140 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_141 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_142 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_143 j)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
