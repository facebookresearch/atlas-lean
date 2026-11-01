/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinPrimitivePackedReplayGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinLiteralQReplaySourcePacket04Part02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinFastQMaskCentral

/-! Sixteen bounded chronological primitive steps, all full Q coordinate images. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_032 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 32 j := by
  change ∀ j : Fin 24, 32 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 32)
      (generatedNinthLowerSpinSourceQReplayWord 4 32 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 33 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_02 (0 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 32 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part02.getD 0 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_02_032,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_02_033, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_033 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 33 j := by
  change ∀ j : Fin 24, 33 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 33)
      (generatedNinthLowerSpinSourceQReplayWord 4 33 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 34 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_02 (1 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 33 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part02.getD 1 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_02_033,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_02_034, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_034 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 34 j := by
  change ∀ j : Fin 24, 34 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 34)
      (generatedNinthLowerSpinSourceQReplayWord 4 34 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 35 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_02 (2 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 34 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part02.getD 2 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_02_034,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_02_035, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_035 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 35 j := by
  change ∀ j : Fin 24, 35 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 35)
      (generatedNinthLowerSpinSourceQReplayWord 4 35 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 36 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_02 (3 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 35 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part02.getD 3 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_02_035,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_02_036, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_036 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 36 j := by
  change ∀ j : Fin 24, 36 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 36)
      (generatedNinthLowerSpinSourceQReplayWord 4 36 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 37 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_02 (4 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 36 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part02.getD 4 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_02_036,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_02_037, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_037 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 37 j := by
  change ∀ j : Fin 24, 37 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 37)
      (generatedNinthLowerSpinSourceQReplayWord 4 37 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 38 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_02 (5 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 37 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part02.getD 5 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_02_037,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_02_038, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_038 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 38 j := by
  change ∀ j : Fin 24, 38 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 38)
      (generatedNinthLowerSpinSourceQReplayWord 4 38 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 39 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_02 (6 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 38 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part02.getD 6 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_02_038,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_02_039, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_039 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 39 j := by
  change ∀ j : Fin 24, 39 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 39)
      (generatedNinthLowerSpinSourceQReplayWord 4 39 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 40 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_02 (7 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 39 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part02.getD 7 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_02_039,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_02_040, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_040 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 40 j := by
  change ∀ j : Fin 24, 40 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 40)
      (generatedNinthLowerSpinSourceQReplayWord 4 40 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 41 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_02 (8 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 40 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part02.getD 8 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_02_040,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_02_041, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_041 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 41 j := by
  change ∀ j : Fin 24, 41 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 41)
      (generatedNinthLowerSpinSourceQReplayWord 4 41 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 42 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_02 (9 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 41 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part02.getD 9 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_02_041,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_02_042, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_042 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 42 j := by
  change ∀ j : Fin 24, 42 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 42)
      (generatedNinthLowerSpinSourceQReplayWord 4 42 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 43 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_02 (10 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 42 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part02.getD 10 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_02_042,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_02_043, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_043 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 43 j := by
  change ∀ j : Fin 24, 43 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 43)
      (generatedNinthLowerSpinSourceQReplayWord 4 43 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 44 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_02 (11 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 43 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part02.getD 11 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_02_043,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_02_044, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_044 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 44 j := by
  change ∀ j : Fin 24, 44 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 44)
      (generatedNinthLowerSpinSourceQReplayWord 4 44 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 45 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_02 (12 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 44 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part02.getD 12 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_02_044,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_02_045, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_045 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 45 j := by
  change ∀ j : Fin 24, 45 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 45)
      (generatedNinthLowerSpinSourceQReplayWord 4 45 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 46 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_02 (13 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 45 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part02.getD 13 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_02_045,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_02_046, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_046 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 46 j := by
  change ∀ j : Fin 24, 46 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 46)
      (generatedNinthLowerSpinSourceQReplayWord 4 46 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 47 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_02 (14 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 46 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part02.getD 14 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_02_046,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_02_047, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_047 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 47 j := by
  change ∀ j : Fin 24, 47 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 47)
      (generatedNinthLowerSpinSourceQReplayWord 4 47 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 48 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_02 (15 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 47 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part02.getD 15 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_02_047,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_02_048, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

/-- Every actual primitive in this sixteen-step block retains all full central coordinates. -/
theorem generatedNinth_lower_spin_source_q_replay_packet_04_part_02 :
    ∀ n : Fin 16, ∀ j : Fin 24,
      32 + n.val < 175 →
        generatedNinthLowerSpinSourceQReplayStepCondition 4
          ⟨32 + n.val, by omega⟩ j := by
  intro n j hn
  fin_cases n
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_032 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_033 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_034 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_035 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_036 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_037 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_038 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_039 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_040 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_041 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_042 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_043 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_044 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_045 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_046 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_047 j)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
