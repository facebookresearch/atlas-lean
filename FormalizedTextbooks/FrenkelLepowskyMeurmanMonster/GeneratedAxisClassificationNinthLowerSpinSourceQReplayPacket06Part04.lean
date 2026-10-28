/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinPrimitivePackedReplayGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinLiteralQReplaySourcePacket06Part04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinFastQMaskCentral

/-! Sixteen bounded chronological primitive steps, all full Q coordinate images. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_064 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 64 j := by
  change ∀ j : Fin 24, 64 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 64)
      (generatedNinthLowerSpinSourceQReplayWord 6 64 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 65 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_04 (0 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 64 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part04.getD 0 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_04_064,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_04_065, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_065 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 65 j := by
  change ∀ j : Fin 24, 65 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 65)
      (generatedNinthLowerSpinSourceQReplayWord 6 65 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 66 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_04 (1 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 65 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part04.getD 1 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_04_065,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_04_066, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_066 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 66 j := by
  change ∀ j : Fin 24, 66 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 66)
      (generatedNinthLowerSpinSourceQReplayWord 6 66 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 67 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_04 (2 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 66 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part04.getD 2 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_04_066,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_04_067, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_067 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 67 j := by
  change ∀ j : Fin 24, 67 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 67)
      (generatedNinthLowerSpinSourceQReplayWord 6 67 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 68 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_04 (3 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 67 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part04.getD 3 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_04_067,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_04_068, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_068 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 68 j := by
  change ∀ j : Fin 24, 68 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 68)
      (generatedNinthLowerSpinSourceQReplayWord 6 68 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 69 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_04 (4 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 68 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part04.getD 4 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_04_068,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_04_069, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_069 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 69 j := by
  change ∀ j : Fin 24, 69 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 69)
      (generatedNinthLowerSpinSourceQReplayWord 6 69 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 70 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_04 (5 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 69 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part04.getD 5 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_04_069,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_04_070, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_070 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 70 j := by
  change ∀ j : Fin 24, 70 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 70)
      (generatedNinthLowerSpinSourceQReplayWord 6 70 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 71 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_04 (6 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 70 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part04.getD 6 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_04_070,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_04_071, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_071 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 71 j := by
  change ∀ j : Fin 24, 71 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 71)
      (generatedNinthLowerSpinSourceQReplayWord 6 71 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 72 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_04 (7 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 71 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part04.getD 7 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_04_071,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_04_072, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_072 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 72 j := by
  change ∀ j : Fin 24, 72 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 72)
      (generatedNinthLowerSpinSourceQReplayWord 6 72 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 73 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_04 (8 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 72 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part04.getD 8 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_04_072,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_04_073, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_073 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 73 j := by
  change ∀ j : Fin 24, 73 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 73)
      (generatedNinthLowerSpinSourceQReplayWord 6 73 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 74 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_04 (9 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 73 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part04.getD 9 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_04_073,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_04_074, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_074 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 74 j := by
  change ∀ j : Fin 24, 74 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 74)
      (generatedNinthLowerSpinSourceQReplayWord 6 74 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 75 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_04 (10 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 74 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part04.getD 10 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_04_074,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_04_075, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_075 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 75 j := by
  change ∀ j : Fin 24, 75 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 75)
      (generatedNinthLowerSpinSourceQReplayWord 6 75 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 76 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_04 (11 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 75 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part04.getD 11 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_04_075,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_04_076, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_076 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 76 j := by
  change ∀ j : Fin 24, 76 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 76)
      (generatedNinthLowerSpinSourceQReplayWord 6 76 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 77 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_04 (12 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 76 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part04.getD 12 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_04_076,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_04_077, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_077 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 77 j := by
  change ∀ j : Fin 24, 77 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 77)
      (generatedNinthLowerSpinSourceQReplayWord 6 77 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 78 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_04 (13 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 77 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part04.getD 13 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_04_077,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_04_078, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_078 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 78 j := by
  change ∀ j : Fin 24, 78 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 78)
      (generatedNinthLowerSpinSourceQReplayWord 6 78 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 79 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_04 (14 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 78 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part04.getD 14 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_04_078,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_04_079, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_079 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 79 j := by
  change ∀ j : Fin 24, 79 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 79)
      (generatedNinthLowerSpinSourceQReplayWord 6 79 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 80 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_04 (15 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 79 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part04.getD 15 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_04_079,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_04_080, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

/-- Every actual primitive in this sixteen-step block retains all full central coordinates. -/
theorem generatedNinth_lower_spin_source_q_replay_packet_06_part_04 :
    ∀ n : Fin 16, ∀ j : Fin 24,
      64 + n.val < 242 →
        generatedNinthLowerSpinSourceQReplayStepCondition 6
          ⟨64 + n.val, by omega⟩ j := by
  intro n j hn
  fin_cases n
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_064 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_065 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_066 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_067 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_068 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_069 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_070 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_071 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_072 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_073 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_074 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_075 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_076 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_077 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_078 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_079 j)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
