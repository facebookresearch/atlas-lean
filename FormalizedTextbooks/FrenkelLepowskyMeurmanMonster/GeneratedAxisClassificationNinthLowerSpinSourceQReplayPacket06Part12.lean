/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinPrimitivePackedReplayGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinLiteralQReplaySourcePacket06Part12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinFastQMaskCentral

/-! Sixteen bounded chronological primitive steps, all full Q coordinate images. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_192 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 192 j := by
  change ∀ j : Fin 24, 192 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 192)
      (generatedNinthLowerSpinSourceQReplayWord 6 192 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 193 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_12 (0 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 192 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part12.getD 0 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_12_192,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_12_193, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_193 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 193 j := by
  change ∀ j : Fin 24, 193 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 193)
      (generatedNinthLowerSpinSourceQReplayWord 6 193 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 194 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_12 (1 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 193 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part12.getD 1 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_12_193,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_12_194, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_194 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 194 j := by
  change ∀ j : Fin 24, 194 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 194)
      (generatedNinthLowerSpinSourceQReplayWord 6 194 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 195 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_12 (2 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 194 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part12.getD 2 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_12_194,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_12_195, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_195 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 195 j := by
  change ∀ j : Fin 24, 195 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 195)
      (generatedNinthLowerSpinSourceQReplayWord 6 195 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 196 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_12 (3 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 195 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part12.getD 3 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_12_195,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_12_196, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_196 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 196 j := by
  change ∀ j : Fin 24, 196 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 196)
      (generatedNinthLowerSpinSourceQReplayWord 6 196 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 197 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_12 (4 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 196 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part12.getD 4 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_12_196,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_12_197, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_197 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 197 j := by
  change ∀ j : Fin 24, 197 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 197)
      (generatedNinthLowerSpinSourceQReplayWord 6 197 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 198 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_12 (5 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 197 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part12.getD 5 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_12_197,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_12_198, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_198 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 198 j := by
  change ∀ j : Fin 24, 198 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 198)
      (generatedNinthLowerSpinSourceQReplayWord 6 198 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 199 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_12 (6 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 198 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part12.getD 6 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_12_198,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_12_199, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_199 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 199 j := by
  change ∀ j : Fin 24, 199 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 199)
      (generatedNinthLowerSpinSourceQReplayWord 6 199 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 200 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_12 (7 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 199 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part12.getD 7 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_12_199,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_12_200, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_200 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 200 j := by
  change ∀ j : Fin 24, 200 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 200)
      (generatedNinthLowerSpinSourceQReplayWord 6 200 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 201 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_12 (8 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 200 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part12.getD 8 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_12_200,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_12_201, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_201 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 201 j := by
  change ∀ j : Fin 24, 201 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 201)
      (generatedNinthLowerSpinSourceQReplayWord 6 201 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 202 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_12 (9 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 201 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part12.getD 9 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_12_201,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_12_202, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_202 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 202 j := by
  change ∀ j : Fin 24, 202 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 202)
      (generatedNinthLowerSpinSourceQReplayWord 6 202 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 203 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_12 (10 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 202 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part12.getD 10 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_12_202,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_12_203, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_203 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 203 j := by
  change ∀ j : Fin 24, 203 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 203)
      (generatedNinthLowerSpinSourceQReplayWord 6 203 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 204 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_12 (11 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 203 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part12.getD 11 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_12_203,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_12_204, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_204 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 204 j := by
  change ∀ j : Fin 24, 204 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 204)
      (generatedNinthLowerSpinSourceQReplayWord 6 204 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 205 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_12 (12 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 204 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part12.getD 12 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_12_204,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_12_205, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_205 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 205 j := by
  change ∀ j : Fin 24, 205 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 205)
      (generatedNinthLowerSpinSourceQReplayWord 6 205 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 206 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_12 (13 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 205 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part12.getD 13 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_12_205,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_12_206, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_206 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 206 j := by
  change ∀ j : Fin 24, 206 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 206)
      (generatedNinthLowerSpinSourceQReplayWord 6 206 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 207 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_12 (14 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 206 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part12.getD 14 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_12_206,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_12_207, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_207 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 207 j := by
  change ∀ j : Fin 24, 207 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 207)
      (generatedNinthLowerSpinSourceQReplayWord 6 207 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 208 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_12 (15 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 207 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part12.getD 15 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_12_207,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_12_208, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

/-- Every actual primitive in this sixteen-step block retains all full central coordinates. -/
theorem generatedNinth_lower_spin_source_q_replay_packet_06_part_12 :
    ∀ n : Fin 16, ∀ j : Fin 24,
      192 + n.val < 242 →
        generatedNinthLowerSpinSourceQReplayStepCondition 6
          ⟨192 + n.val, by omega⟩ j := by
  intro n j hn
  fin_cases n
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_192 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_193 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_194 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_195 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_196 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_197 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_198 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_199 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_200 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_201 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_202 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_203 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_204 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_205 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_206 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_207 j)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
