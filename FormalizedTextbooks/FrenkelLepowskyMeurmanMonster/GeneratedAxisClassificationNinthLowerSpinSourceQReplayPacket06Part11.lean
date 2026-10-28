/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinPrimitivePackedReplayGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinLiteralQReplaySourcePacket06Part11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinFastQMaskCentral

/-! Sixteen bounded chronological primitive steps, all full Q coordinate images. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_176 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 176 j := by
  change ∀ j : Fin 24, 176 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 176)
      (generatedNinthLowerSpinSourceQReplayWord 6 176 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 177 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_11 (0 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 176 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part11.getD 0 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_11_176,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_11_177, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_177 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 177 j := by
  change ∀ j : Fin 24, 177 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 177)
      (generatedNinthLowerSpinSourceQReplayWord 6 177 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 178 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_11 (1 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 177 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part11.getD 1 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_11_177,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_11_178, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_178 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 178 j := by
  change ∀ j : Fin 24, 178 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 178)
      (generatedNinthLowerSpinSourceQReplayWord 6 178 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 179 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_11 (2 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 178 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part11.getD 2 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_11_178,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_11_179, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_179 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 179 j := by
  change ∀ j : Fin 24, 179 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 179)
      (generatedNinthLowerSpinSourceQReplayWord 6 179 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 180 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_11 (3 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 179 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part11.getD 3 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_11_179,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_11_180, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_180 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 180 j := by
  change ∀ j : Fin 24, 180 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 180)
      (generatedNinthLowerSpinSourceQReplayWord 6 180 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 181 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_11 (4 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 180 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part11.getD 4 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_11_180,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_11_181, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_181 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 181 j := by
  change ∀ j : Fin 24, 181 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 181)
      (generatedNinthLowerSpinSourceQReplayWord 6 181 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 182 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_11 (5 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 181 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part11.getD 5 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_11_181,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_11_182, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_182 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 182 j := by
  change ∀ j : Fin 24, 182 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 182)
      (generatedNinthLowerSpinSourceQReplayWord 6 182 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 183 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_11 (6 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 182 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part11.getD 6 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_11_182,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_11_183, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_183 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 183 j := by
  change ∀ j : Fin 24, 183 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 183)
      (generatedNinthLowerSpinSourceQReplayWord 6 183 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 184 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_11 (7 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 183 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part11.getD 7 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_11_183,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_11_184, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_184 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 184 j := by
  change ∀ j : Fin 24, 184 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 184)
      (generatedNinthLowerSpinSourceQReplayWord 6 184 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 185 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_11 (8 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 184 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part11.getD 8 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_11_184,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_11_185, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_185 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 185 j := by
  change ∀ j : Fin 24, 185 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 185)
      (generatedNinthLowerSpinSourceQReplayWord 6 185 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 186 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_11 (9 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 185 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part11.getD 9 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_11_185,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_11_186, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_186 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 186 j := by
  change ∀ j : Fin 24, 186 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 186)
      (generatedNinthLowerSpinSourceQReplayWord 6 186 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 187 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_11 (10 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 186 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part11.getD 10 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_11_186,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_11_187, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_187 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 187 j := by
  change ∀ j : Fin 24, 187 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 187)
      (generatedNinthLowerSpinSourceQReplayWord 6 187 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 188 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_11 (11 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 187 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part11.getD 11 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_11_187,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_11_188, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_188 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 188 j := by
  change ∀ j : Fin 24, 188 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 188)
      (generatedNinthLowerSpinSourceQReplayWord 6 188 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 189 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_11 (12 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 188 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part11.getD 12 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_11_188,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_11_189, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_189 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 189 j := by
  change ∀ j : Fin 24, 189 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 189)
      (generatedNinthLowerSpinSourceQReplayWord 6 189 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 190 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_11 (13 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 189 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part11.getD 13 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_11_189,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_11_190, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_190 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 190 j := by
  change ∀ j : Fin 24, 190 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 190)
      (generatedNinthLowerSpinSourceQReplayWord 6 190 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 191 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_11 (14 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 190 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part11.getD 14 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_11_190,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_11_191, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_191 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 191 j := by
  change ∀ j : Fin 24, 191 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 191)
      (generatedNinthLowerSpinSourceQReplayWord 6 191 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 192 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_11 (15 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 191 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part11.getD 15 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_11_191,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_11_192, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

/-- Every actual primitive in this sixteen-step block retains all full central coordinates. -/
theorem generatedNinth_lower_spin_source_q_replay_packet_06_part_11 :
    ∀ n : Fin 16, ∀ j : Fin 24,
      176 + n.val < 242 →
        generatedNinthLowerSpinSourceQReplayStepCondition 6
          ⟨176 + n.val, by omega⟩ j := by
  intro n j hn
  fin_cases n
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_176 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_177 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_178 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_179 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_180 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_181 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_182 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_183 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_184 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_185 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_186 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_187 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_188 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_189 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_190 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_191 j)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
