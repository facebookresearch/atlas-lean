/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinPrimitivePackedReplayGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinLiteralQReplaySourcePacket04Part05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinFastQMaskCentral

/-! Sixteen bounded chronological primitive steps, all full Q coordinate images. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_080 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 80 j := by
  change ∀ j : Fin 24, 80 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 80)
      (generatedNinthLowerSpinSourceQReplayWord 4 80 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 81 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_05 (0 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 80 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part05.getD 0 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_05_080,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_05_081, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_081 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 81 j := by
  change ∀ j : Fin 24, 81 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 81)
      (generatedNinthLowerSpinSourceQReplayWord 4 81 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 82 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_05 (1 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 81 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part05.getD 1 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_05_081,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_05_082, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_082 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 82 j := by
  change ∀ j : Fin 24, 82 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 82)
      (generatedNinthLowerSpinSourceQReplayWord 4 82 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 83 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_05 (2 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 82 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part05.getD 2 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_05_082,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_05_083, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_083 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 83 j := by
  change ∀ j : Fin 24, 83 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 83)
      (generatedNinthLowerSpinSourceQReplayWord 4 83 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 84 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_05 (3 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 83 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part05.getD 3 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_05_083,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_05_084, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_084 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 84 j := by
  change ∀ j : Fin 24, 84 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 84)
      (generatedNinthLowerSpinSourceQReplayWord 4 84 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 85 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_05 (4 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 84 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part05.getD 4 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_05_084,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_05_085, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_085 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 85 j := by
  change ∀ j : Fin 24, 85 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 85)
      (generatedNinthLowerSpinSourceQReplayWord 4 85 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 86 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_05 (5 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 85 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part05.getD 5 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_05_085,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_05_086, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_086 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 86 j := by
  change ∀ j : Fin 24, 86 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 86)
      (generatedNinthLowerSpinSourceQReplayWord 4 86 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 87 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_05 (6 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 86 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part05.getD 6 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_05_086,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_05_087, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_087 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 87 j := by
  change ∀ j : Fin 24, 87 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 87)
      (generatedNinthLowerSpinSourceQReplayWord 4 87 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 88 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_05 (7 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 87 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part05.getD 7 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_05_087,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_05_088, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_088 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 88 j := by
  change ∀ j : Fin 24, 88 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 88)
      (generatedNinthLowerSpinSourceQReplayWord 4 88 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 89 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_05 (8 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 88 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part05.getD 8 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_05_088,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_05_089, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_089 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 89 j := by
  change ∀ j : Fin 24, 89 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 89)
      (generatedNinthLowerSpinSourceQReplayWord 4 89 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 90 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_05 (9 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 89 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part05.getD 9 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_05_089,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_05_090, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_090 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 90 j := by
  change ∀ j : Fin 24, 90 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 90)
      (generatedNinthLowerSpinSourceQReplayWord 4 90 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 91 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_05 (10 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 90 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part05.getD 10 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_05_090,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_05_091, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_091 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 91 j := by
  change ∀ j : Fin 24, 91 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 91)
      (generatedNinthLowerSpinSourceQReplayWord 4 91 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 92 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_05 (11 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 91 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part05.getD 11 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_05_091,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_05_092, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_092 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 92 j := by
  change ∀ j : Fin 24, 92 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 92)
      (generatedNinthLowerSpinSourceQReplayWord 4 92 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 93 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_05 (12 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 92 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part05.getD 12 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_05_092,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_05_093, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_093 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 93 j := by
  change ∀ j : Fin 24, 93 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 93)
      (generatedNinthLowerSpinSourceQReplayWord 4 93 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 94 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_05 (13 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 93 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part05.getD 13 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_05_093,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_05_094, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_094 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 94 j := by
  change ∀ j : Fin 24, 94 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 94)
      (generatedNinthLowerSpinSourceQReplayWord 4 94 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 95 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_05 (14 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 94 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part05.getD 14 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_05_094,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_05_095, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_095 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 95 j := by
  change ∀ j : Fin 24, 95 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 95)
      (generatedNinthLowerSpinSourceQReplayWord 4 95 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 96 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_05 (15 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 95 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part05.getD 15 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_05_095,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_05_096, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

/-- Every actual primitive in this sixteen-step block retains all full central coordinates. -/
theorem generatedNinth_lower_spin_source_q_replay_packet_04_part_05 :
    ∀ n : Fin 16, ∀ j : Fin 24,
      80 + n.val < 175 →
        generatedNinthLowerSpinSourceQReplayStepCondition 4
          ⟨80 + n.val, by omega⟩ j := by
  intro n j hn
  fin_cases n
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_080 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_081 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_082 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_083 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_084 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_085 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_086 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_087 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_088 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_089 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_090 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_091 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_092 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_093 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_094 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_095 j)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
