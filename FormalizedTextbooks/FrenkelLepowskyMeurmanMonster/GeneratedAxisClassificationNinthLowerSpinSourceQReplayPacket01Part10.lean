/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinPrimitivePackedReplayGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinLiteralQReplaySourcePacket01Part10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinFastQMaskCentral

/-! Sixteen bounded chronological primitive steps, all full Q coordinate images. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_160 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 1 160 j := by
  change ∀ j : Fin 24, 160 < (generatedNinthLowerSpinSourceWord 1).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 1 160)
      (generatedNinthLowerSpinSourceQReplayWord 1 160 j)
      (generatedNinthLowerSpinSourceQReplayWord 1 161 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_01_part_10 (0 : Fin 13)
  change generatedNinthLowerSpinSourceQReplayLetter 1 160 =
    generatedNinthLowerSpinLiteralQReplayLetters01Part10.getD 0 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_01_part_10_160,
    generatedNinth_lower_spin_literal_q_replay_prefix_01_part_10_161, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_161 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 1 161 j := by
  change ∀ j : Fin 24, 161 < (generatedNinthLowerSpinSourceWord 1).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 1 161)
      (generatedNinthLowerSpinSourceQReplayWord 1 161 j)
      (generatedNinthLowerSpinSourceQReplayWord 1 162 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_01_part_10 (1 : Fin 13)
  change generatedNinthLowerSpinSourceQReplayLetter 1 161 =
    generatedNinthLowerSpinLiteralQReplayLetters01Part10.getD 1 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_01_part_10_161,
    generatedNinth_lower_spin_literal_q_replay_prefix_01_part_10_162, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_162 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 1 162 j := by
  change ∀ j : Fin 24, 162 < (generatedNinthLowerSpinSourceWord 1).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 1 162)
      (generatedNinthLowerSpinSourceQReplayWord 1 162 j)
      (generatedNinthLowerSpinSourceQReplayWord 1 163 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_01_part_10 (2 : Fin 13)
  change generatedNinthLowerSpinSourceQReplayLetter 1 162 =
    generatedNinthLowerSpinLiteralQReplayLetters01Part10.getD 2 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_01_part_10_162,
    generatedNinth_lower_spin_literal_q_replay_prefix_01_part_10_163, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_163 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 1 163 j := by
  change ∀ j : Fin 24, 163 < (generatedNinthLowerSpinSourceWord 1).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 1 163)
      (generatedNinthLowerSpinSourceQReplayWord 1 163 j)
      (generatedNinthLowerSpinSourceQReplayWord 1 164 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_01_part_10 (3 : Fin 13)
  change generatedNinthLowerSpinSourceQReplayLetter 1 163 =
    generatedNinthLowerSpinLiteralQReplayLetters01Part10.getD 3 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_01_part_10_163,
    generatedNinth_lower_spin_literal_q_replay_prefix_01_part_10_164, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_164 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 1 164 j := by
  change ∀ j : Fin 24, 164 < (generatedNinthLowerSpinSourceWord 1).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 1 164)
      (generatedNinthLowerSpinSourceQReplayWord 1 164 j)
      (generatedNinthLowerSpinSourceQReplayWord 1 165 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_01_part_10 (4 : Fin 13)
  change generatedNinthLowerSpinSourceQReplayLetter 1 164 =
    generatedNinthLowerSpinLiteralQReplayLetters01Part10.getD 4 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_01_part_10_164,
    generatedNinth_lower_spin_literal_q_replay_prefix_01_part_10_165, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_165 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 1 165 j := by
  change ∀ j : Fin 24, 165 < (generatedNinthLowerSpinSourceWord 1).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 1 165)
      (generatedNinthLowerSpinSourceQReplayWord 1 165 j)
      (generatedNinthLowerSpinSourceQReplayWord 1 166 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_01_part_10 (5 : Fin 13)
  change generatedNinthLowerSpinSourceQReplayLetter 1 165 =
    generatedNinthLowerSpinLiteralQReplayLetters01Part10.getD 5 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_01_part_10_165,
    generatedNinth_lower_spin_literal_q_replay_prefix_01_part_10_166, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_166 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 1 166 j := by
  change ∀ j : Fin 24, 166 < (generatedNinthLowerSpinSourceWord 1).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 1 166)
      (generatedNinthLowerSpinSourceQReplayWord 1 166 j)
      (generatedNinthLowerSpinSourceQReplayWord 1 167 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_01_part_10 (6 : Fin 13)
  change generatedNinthLowerSpinSourceQReplayLetter 1 166 =
    generatedNinthLowerSpinLiteralQReplayLetters01Part10.getD 6 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_01_part_10_166,
    generatedNinth_lower_spin_literal_q_replay_prefix_01_part_10_167, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_167 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 1 167 j := by
  change ∀ j : Fin 24, 167 < (generatedNinthLowerSpinSourceWord 1).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 1 167)
      (generatedNinthLowerSpinSourceQReplayWord 1 167 j)
      (generatedNinthLowerSpinSourceQReplayWord 1 168 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_01_part_10 (7 : Fin 13)
  change generatedNinthLowerSpinSourceQReplayLetter 1 167 =
    generatedNinthLowerSpinLiteralQReplayLetters01Part10.getD 7 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_01_part_10_167,
    generatedNinth_lower_spin_literal_q_replay_prefix_01_part_10_168, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_168 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 1 168 j := by
  change ∀ j : Fin 24, 168 < (generatedNinthLowerSpinSourceWord 1).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 1 168)
      (generatedNinthLowerSpinSourceQReplayWord 1 168 j)
      (generatedNinthLowerSpinSourceQReplayWord 1 169 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_01_part_10 (8 : Fin 13)
  change generatedNinthLowerSpinSourceQReplayLetter 1 168 =
    generatedNinthLowerSpinLiteralQReplayLetters01Part10.getD 8 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_01_part_10_168,
    generatedNinth_lower_spin_literal_q_replay_prefix_01_part_10_169, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_169 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 1 169 j := by
  change ∀ j : Fin 24, 169 < (generatedNinthLowerSpinSourceWord 1).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 1 169)
      (generatedNinthLowerSpinSourceQReplayWord 1 169 j)
      (generatedNinthLowerSpinSourceQReplayWord 1 170 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_01_part_10 (9 : Fin 13)
  change generatedNinthLowerSpinSourceQReplayLetter 1 169 =
    generatedNinthLowerSpinLiteralQReplayLetters01Part10.getD 9 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_01_part_10_169,
    generatedNinth_lower_spin_literal_q_replay_prefix_01_part_10_170, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_170 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 1 170 j := by
  change ∀ j : Fin 24, 170 < (generatedNinthLowerSpinSourceWord 1).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 1 170)
      (generatedNinthLowerSpinSourceQReplayWord 1 170 j)
      (generatedNinthLowerSpinSourceQReplayWord 1 171 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_01_part_10 (10 : Fin 13)
  change generatedNinthLowerSpinSourceQReplayLetter 1 170 =
    generatedNinthLowerSpinLiteralQReplayLetters01Part10.getD 10 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_01_part_10_170,
    generatedNinth_lower_spin_literal_q_replay_prefix_01_part_10_171, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_171 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 1 171 j := by
  change ∀ j : Fin 24, 171 < (generatedNinthLowerSpinSourceWord 1).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 1 171)
      (generatedNinthLowerSpinSourceQReplayWord 1 171 j)
      (generatedNinthLowerSpinSourceQReplayWord 1 172 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_01_part_10 (11 : Fin 13)
  change generatedNinthLowerSpinSourceQReplayLetter 1 171 =
    generatedNinthLowerSpinLiteralQReplayLetters01Part10.getD 11 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_01_part_10_171,
    generatedNinth_lower_spin_literal_q_replay_prefix_01_part_10_172, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_172 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 1 172 j := by
  change ∀ j : Fin 24, 172 < (generatedNinthLowerSpinSourceWord 1).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 1 172)
      (generatedNinthLowerSpinSourceQReplayWord 1 172 j)
      (generatedNinthLowerSpinSourceQReplayWord 1 173 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_01_part_10 (12 : Fin 13)
  change generatedNinthLowerSpinSourceQReplayLetter 1 172 =
    generatedNinthLowerSpinLiteralQReplayLetters01Part10.getD 12 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_01_part_10_172,
    generatedNinth_lower_spin_literal_q_replay_prefix_01_part_10_173, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

/-- Every actual primitive in this sixteen-step block retains all full central coordinates. -/
theorem generatedNinth_lower_spin_source_q_replay_packet_01_part_10 :
    ∀ n : Fin 16, ∀ j : Fin 24,
      160 + n.val < 173 →
        generatedNinthLowerSpinSourceQReplayStepCondition 1
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
  · norm_num at hn
  · norm_num at hn
  · norm_num at hn

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
