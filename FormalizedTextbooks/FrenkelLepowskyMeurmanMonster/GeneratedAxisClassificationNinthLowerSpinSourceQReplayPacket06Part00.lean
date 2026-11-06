/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinPrimitivePackedReplayGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinLiteralQReplaySourcePacket06Part00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinFastQMaskCentral

/-! Sixteen bounded chronological primitive steps, all full Q coordinate images. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_000 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 0 j := by
  change ∀ j : Fin 24, 0 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 0)
      (generatedNinthLowerSpinSourceQReplayWord 6 0 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 1 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_00 (0 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 0 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part00.getD 0 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_00_000,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_00_001, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_001 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 1 j := by
  change ∀ j : Fin 24, 1 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 1)
      (generatedNinthLowerSpinSourceQReplayWord 6 1 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 2 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_00 (1 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 1 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part00.getD 1 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_00_001,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_00_002, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_002 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 2 j := by
  change ∀ j : Fin 24, 2 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 2)
      (generatedNinthLowerSpinSourceQReplayWord 6 2 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 3 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_00 (2 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 2 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part00.getD 2 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_00_002,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_00_003, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_003 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 3 j := by
  change ∀ j : Fin 24, 3 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 3)
      (generatedNinthLowerSpinSourceQReplayWord 6 3 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 4 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_00 (3 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 3 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part00.getD 3 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_00_003,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_00_004, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_004 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 4 j := by
  change ∀ j : Fin 24, 4 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 4)
      (generatedNinthLowerSpinSourceQReplayWord 6 4 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 5 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_00 (4 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 4 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part00.getD 4 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_00_004,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_00_005, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_005 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 5 j := by
  change ∀ j : Fin 24, 5 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 5)
      (generatedNinthLowerSpinSourceQReplayWord 6 5 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 6 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_00 (5 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 5 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part00.getD 5 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_00_005,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_00_006, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_006 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 6 j := by
  change ∀ j : Fin 24, 6 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 6)
      (generatedNinthLowerSpinSourceQReplayWord 6 6 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 7 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_00 (6 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 6 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part00.getD 6 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_00_006,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_00_007, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_007 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 7 j := by
  change ∀ j : Fin 24, 7 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 7)
      (generatedNinthLowerSpinSourceQReplayWord 6 7 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 8 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_00 (7 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 7 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part00.getD 7 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_00_007,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_00_008, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_008 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 8 j := by
  change ∀ j : Fin 24, 8 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 8)
      (generatedNinthLowerSpinSourceQReplayWord 6 8 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 9 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_00 (8 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 8 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part00.getD 8 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_00_008,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_00_009, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_009 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 9 j := by
  change ∀ j : Fin 24, 9 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 9)
      (generatedNinthLowerSpinSourceQReplayWord 6 9 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 10 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_00 (9 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 9 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part00.getD 9 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_00_009,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_00_010, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_010 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 10 j := by
  change ∀ j : Fin 24, 10 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 10)
      (generatedNinthLowerSpinSourceQReplayWord 6 10 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 11 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_00 (10 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 10 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part00.getD 10 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_00_010,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_00_011, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_011 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 11 j := by
  change ∀ j : Fin 24, 11 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 11)
      (generatedNinthLowerSpinSourceQReplayWord 6 11 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 12 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_00 (11 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 11 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part00.getD 11 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_00_011,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_00_012, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_012 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 12 j := by
  change ∀ j : Fin 24, 12 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 12)
      (generatedNinthLowerSpinSourceQReplayWord 6 12 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 13 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_00 (12 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 12 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part00.getD 12 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_00_012,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_00_013, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_013 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 13 j := by
  change ∀ j : Fin 24, 13 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 13)
      (generatedNinthLowerSpinSourceQReplayWord 6 13 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 14 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_00 (13 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 13 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part00.getD 13 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_00_013,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_00_014, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_014 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 14 j := by
  change ∀ j : Fin 24, 14 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 14)
      (generatedNinthLowerSpinSourceQReplayWord 6 14 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 15 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_00 (14 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 14 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part00.getD 14 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_00_014,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_00_015, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_015 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 15 j := by
  change ∀ j : Fin 24, 15 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 15)
      (generatedNinthLowerSpinSourceQReplayWord 6 15 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 16 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_00 (15 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 15 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part00.getD 15 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_00_015,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_00_016, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

/-- Every actual primitive in this sixteen-step block retains all full central coordinates. -/
theorem generatedNinth_lower_spin_source_q_replay_packet_06_part_00 :
    ∀ n : Fin 16, ∀ j : Fin 24,
      0 + n.val < 242 →
        generatedNinthLowerSpinSourceQReplayStepCondition 6
          ⟨0 + n.val, by omega⟩ j := by
  intro n j hn
  fin_cases n
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_000 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_001 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_002 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_003 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_004 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_005 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_006 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_007 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_008 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_009 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_010 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_011 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_012 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_013 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_014 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_015 j)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
