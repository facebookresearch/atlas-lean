/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinPrimitivePackedReplayGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinLiteralQReplaySourcePacket06Part10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinFastQMaskCentral

/-! Sixteen bounded chronological primitive steps, all full Q coordinate images. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_160 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 160 j := by
  change ∀ j : Fin 24, 160 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 160)
      (generatedNinthLowerSpinSourceQReplayWord 6 160 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 161 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_10 (0 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 160 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part10.getD 0 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_10_160,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_10_161, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_161 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 161 j := by
  change ∀ j : Fin 24, 161 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 161)
      (generatedNinthLowerSpinSourceQReplayWord 6 161 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 162 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_10 (1 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 161 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part10.getD 1 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_10_161,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_10_162, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_162 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 162 j := by
  change ∀ j : Fin 24, 162 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 162)
      (generatedNinthLowerSpinSourceQReplayWord 6 162 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 163 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_10 (2 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 162 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part10.getD 2 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_10_162,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_10_163, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_163 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 163 j := by
  change ∀ j : Fin 24, 163 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 163)
      (generatedNinthLowerSpinSourceQReplayWord 6 163 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 164 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_10 (3 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 163 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part10.getD 3 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_10_163,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_10_164, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_164 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 164 j := by
  change ∀ j : Fin 24, 164 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 164)
      (generatedNinthLowerSpinSourceQReplayWord 6 164 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 165 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_10 (4 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 164 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part10.getD 4 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_10_164,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_10_165, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_165 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 165 j := by
  change ∀ j : Fin 24, 165 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 165)
      (generatedNinthLowerSpinSourceQReplayWord 6 165 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 166 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_10 (5 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 165 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part10.getD 5 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_10_165,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_10_166, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_166 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 166 j := by
  change ∀ j : Fin 24, 166 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 166)
      (generatedNinthLowerSpinSourceQReplayWord 6 166 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 167 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_10 (6 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 166 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part10.getD 6 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_10_166,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_10_167, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_167 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 167 j := by
  change ∀ j : Fin 24, 167 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 167)
      (generatedNinthLowerSpinSourceQReplayWord 6 167 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 168 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_10 (7 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 167 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part10.getD 7 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_10_167,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_10_168, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_168 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 168 j := by
  change ∀ j : Fin 24, 168 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 168)
      (generatedNinthLowerSpinSourceQReplayWord 6 168 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 169 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_10 (8 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 168 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part10.getD 8 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_10_168,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_10_169, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_169 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 169 j := by
  change ∀ j : Fin 24, 169 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 169)
      (generatedNinthLowerSpinSourceQReplayWord 6 169 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 170 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_10 (9 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 169 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part10.getD 9 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_10_169,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_10_170, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_170 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 170 j := by
  change ∀ j : Fin 24, 170 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 170)
      (generatedNinthLowerSpinSourceQReplayWord 6 170 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 171 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_10 (10 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 170 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part10.getD 10 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_10_170,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_10_171, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_171 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 171 j := by
  change ∀ j : Fin 24, 171 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 171)
      (generatedNinthLowerSpinSourceQReplayWord 6 171 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 172 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_10 (11 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 171 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part10.getD 11 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_10_171,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_10_172, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_172 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 172 j := by
  change ∀ j : Fin 24, 172 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 172)
      (generatedNinthLowerSpinSourceQReplayWord 6 172 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 173 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_10 (12 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 172 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part10.getD 12 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_10_172,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_10_173, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_173 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 173 j := by
  change ∀ j : Fin 24, 173 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 173)
      (generatedNinthLowerSpinSourceQReplayWord 6 173 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 174 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_10 (13 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 173 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part10.getD 13 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_10_173,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_10_174, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_174 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 174 j := by
  change ∀ j : Fin 24, 174 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 174)
      (generatedNinthLowerSpinSourceQReplayWord 6 174 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 175 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_10 (14 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 174 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part10.getD 14 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_10_174,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_10_175, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_175 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 175 j := by
  change ∀ j : Fin 24, 175 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 175)
      (generatedNinthLowerSpinSourceQReplayWord 6 175 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 176 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_10 (15 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 175 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part10.getD 15 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_10_175,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_10_176, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

/-- Every actual primitive in this sixteen-step block retains all full central coordinates. -/
theorem generatedNinth_lower_spin_source_q_replay_packet_06_part_10 :
    ∀ n : Fin 16, ∀ j : Fin 24,
      160 + n.val < 242 →
        generatedNinthLowerSpinSourceQReplayStepCondition 6
          ⟨160 + n.val, by omega⟩ j := by
  intro n j hn
  fin_cases n
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_160 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_161 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_162 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_163 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_164 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_165 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_166 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_167 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_168 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_169 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_170 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_171 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_172 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_173 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_174 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_175 j)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
