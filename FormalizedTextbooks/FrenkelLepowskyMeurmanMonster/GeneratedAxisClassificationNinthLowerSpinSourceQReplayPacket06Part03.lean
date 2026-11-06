/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinPrimitivePackedReplayGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinLiteralQReplaySourcePacket06Part03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinFastQMaskCentral

/-! Sixteen bounded chronological primitive steps, all full Q coordinate images. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_048 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 48 j := by
  change ∀ j : Fin 24, 48 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 48)
      (generatedNinthLowerSpinSourceQReplayWord 6 48 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 49 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_03 (0 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 48 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part03.getD 0 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_03_048,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_03_049, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_049 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 49 j := by
  change ∀ j : Fin 24, 49 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 49)
      (generatedNinthLowerSpinSourceQReplayWord 6 49 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 50 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_03 (1 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 49 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part03.getD 1 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_03_049,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_03_050, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_050 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 50 j := by
  change ∀ j : Fin 24, 50 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 50)
      (generatedNinthLowerSpinSourceQReplayWord 6 50 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 51 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_03 (2 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 50 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part03.getD 2 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_03_050,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_03_051, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_051 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 51 j := by
  change ∀ j : Fin 24, 51 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 51)
      (generatedNinthLowerSpinSourceQReplayWord 6 51 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 52 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_03 (3 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 51 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part03.getD 3 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_03_051,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_03_052, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_052 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 52 j := by
  change ∀ j : Fin 24, 52 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 52)
      (generatedNinthLowerSpinSourceQReplayWord 6 52 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 53 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_03 (4 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 52 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part03.getD 4 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_03_052,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_03_053, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_053 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 53 j := by
  change ∀ j : Fin 24, 53 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 53)
      (generatedNinthLowerSpinSourceQReplayWord 6 53 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 54 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_03 (5 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 53 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part03.getD 5 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_03_053,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_03_054, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_054 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 54 j := by
  change ∀ j : Fin 24, 54 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 54)
      (generatedNinthLowerSpinSourceQReplayWord 6 54 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 55 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_03 (6 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 54 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part03.getD 6 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_03_054,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_03_055, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_055 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 55 j := by
  change ∀ j : Fin 24, 55 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 55)
      (generatedNinthLowerSpinSourceQReplayWord 6 55 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 56 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_03 (7 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 55 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part03.getD 7 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_03_055,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_03_056, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_056 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 56 j := by
  change ∀ j : Fin 24, 56 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 56)
      (generatedNinthLowerSpinSourceQReplayWord 6 56 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 57 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_03 (8 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 56 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part03.getD 8 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_03_056,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_03_057, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_057 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 57 j := by
  change ∀ j : Fin 24, 57 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 57)
      (generatedNinthLowerSpinSourceQReplayWord 6 57 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 58 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_03 (9 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 57 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part03.getD 9 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_03_057,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_03_058, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_058 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 58 j := by
  change ∀ j : Fin 24, 58 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 58)
      (generatedNinthLowerSpinSourceQReplayWord 6 58 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 59 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_03 (10 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 58 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part03.getD 10 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_03_058,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_03_059, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_059 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 59 j := by
  change ∀ j : Fin 24, 59 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 59)
      (generatedNinthLowerSpinSourceQReplayWord 6 59 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 60 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_03 (11 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 59 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part03.getD 11 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_03_059,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_03_060, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_060 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 60 j := by
  change ∀ j : Fin 24, 60 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 60)
      (generatedNinthLowerSpinSourceQReplayWord 6 60 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 61 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_03 (12 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 60 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part03.getD 12 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_03_060,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_03_061, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_061 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 61 j := by
  change ∀ j : Fin 24, 61 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 61)
      (generatedNinthLowerSpinSourceQReplayWord 6 61 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 62 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_03 (13 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 61 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part03.getD 13 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_03_061,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_03_062, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_062 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 62 j := by
  change ∀ j : Fin 24, 62 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 62)
      (generatedNinthLowerSpinSourceQReplayWord 6 62 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 63 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_03 (14 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 62 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part03.getD 14 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_03_062,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_03_063, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_063 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 6 63 j := by
  change ∀ j : Fin 24, 63 < (generatedNinthLowerSpinSourceWord 6).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 6 63)
      (generatedNinthLowerSpinSourceQReplayWord 6 63 j)
      (generatedNinthLowerSpinSourceQReplayWord 6 64 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_06_part_03 (15 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 6 63 =
    generatedNinthLowerSpinLiteralQReplayLetters06Part03.getD 15 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_06_part_03_063,
    generatedNinth_lower_spin_literal_q_replay_prefix_06_part_03_064, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

/-- Every actual primitive in this sixteen-step block retains all full central coordinates. -/
theorem generatedNinth_lower_spin_source_q_replay_packet_06_part_03 :
    ∀ n : Fin 16, ∀ j : Fin 24,
      48 + n.val < 242 →
        generatedNinthLowerSpinSourceQReplayStepCondition 6
          ⟨48 + n.val, by omega⟩ j := by
  intro n j hn
  fin_cases n
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_048 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_049 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_050 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_051 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_052 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_053 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_054 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_055 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_056 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_057 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_058 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_059 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_060 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_061 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_062 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_063 j)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
