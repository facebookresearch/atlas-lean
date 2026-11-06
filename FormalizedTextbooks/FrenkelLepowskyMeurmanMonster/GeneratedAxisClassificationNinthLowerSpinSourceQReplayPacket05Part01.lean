/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinPrimitivePackedReplayGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinLiteralQReplaySourcePacket05Part01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinFastQMaskCentral

/-! Sixteen bounded chronological primitive steps, all full Q coordinate images. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_016 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 16 j := by
  change ∀ j : Fin 24, 16 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 16)
      (generatedNinthLowerSpinSourceQReplayWord 5 16 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 17 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_01 (0 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 16 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part01.getD 0 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_01_016,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_01_017, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_017 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 17 j := by
  change ∀ j : Fin 24, 17 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 17)
      (generatedNinthLowerSpinSourceQReplayWord 5 17 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 18 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_01 (1 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 17 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part01.getD 1 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_01_017,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_01_018, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_018 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 18 j := by
  change ∀ j : Fin 24, 18 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 18)
      (generatedNinthLowerSpinSourceQReplayWord 5 18 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 19 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_01 (2 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 18 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part01.getD 2 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_01_018,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_01_019, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_019 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 19 j := by
  change ∀ j : Fin 24, 19 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 19)
      (generatedNinthLowerSpinSourceQReplayWord 5 19 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 20 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_01 (3 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 19 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part01.getD 3 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_01_019,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_01_020, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_020 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 20 j := by
  change ∀ j : Fin 24, 20 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 20)
      (generatedNinthLowerSpinSourceQReplayWord 5 20 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 21 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_01 (4 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 20 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part01.getD 4 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_01_020,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_01_021, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_021 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 21 j := by
  change ∀ j : Fin 24, 21 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 21)
      (generatedNinthLowerSpinSourceQReplayWord 5 21 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 22 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_01 (5 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 21 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part01.getD 5 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_01_021,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_01_022, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_022 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 22 j := by
  change ∀ j : Fin 24, 22 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 22)
      (generatedNinthLowerSpinSourceQReplayWord 5 22 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 23 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_01 (6 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 22 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part01.getD 6 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_01_022,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_01_023, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_023 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 23 j := by
  change ∀ j : Fin 24, 23 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 23)
      (generatedNinthLowerSpinSourceQReplayWord 5 23 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 24 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_01 (7 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 23 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part01.getD 7 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_01_023,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_01_024, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_024 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 24 j := by
  change ∀ j : Fin 24, 24 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 24)
      (generatedNinthLowerSpinSourceQReplayWord 5 24 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 25 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_01 (8 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 24 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part01.getD 8 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_01_024,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_01_025, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_025 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 25 j := by
  change ∀ j : Fin 24, 25 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 25)
      (generatedNinthLowerSpinSourceQReplayWord 5 25 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 26 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_01 (9 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 25 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part01.getD 9 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_01_025,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_01_026, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_026 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 26 j := by
  change ∀ j : Fin 24, 26 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 26)
      (generatedNinthLowerSpinSourceQReplayWord 5 26 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 27 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_01 (10 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 26 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part01.getD 10 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_01_026,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_01_027, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_027 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 27 j := by
  change ∀ j : Fin 24, 27 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 27)
      (generatedNinthLowerSpinSourceQReplayWord 5 27 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 28 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_01 (11 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 27 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part01.getD 11 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_01_027,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_01_028, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_028 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 28 j := by
  change ∀ j : Fin 24, 28 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 28)
      (generatedNinthLowerSpinSourceQReplayWord 5 28 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 29 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_01 (12 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 28 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part01.getD 12 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_01_028,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_01_029, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_029 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 29 j := by
  change ∀ j : Fin 24, 29 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 29)
      (generatedNinthLowerSpinSourceQReplayWord 5 29 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 30 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_01 (13 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 29 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part01.getD 13 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_01_029,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_01_030, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_030 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 30 j := by
  change ∀ j : Fin 24, 30 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 30)
      (generatedNinthLowerSpinSourceQReplayWord 5 30 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 31 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_01 (14 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 30 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part01.getD 14 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_01_030,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_01_031, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_031 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 31 j := by
  change ∀ j : Fin 24, 31 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 31)
      (generatedNinthLowerSpinSourceQReplayWord 5 31 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 32 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_01 (15 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 31 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part01.getD 15 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_01_031,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_01_032, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

/-- Every actual primitive in this sixteen-step block retains all full central coordinates. -/
theorem generatedNinth_lower_spin_source_q_replay_packet_05_part_01 :
    ∀ n : Fin 16, ∀ j : Fin 24,
      16 + n.val < 314 →
        generatedNinthLowerSpinSourceQReplayStepCondition 5
          ⟨16 + n.val, by omega⟩ j := by
  intro n j hn
  fin_cases n
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_016 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_017 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_018 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_019 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_020 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_021 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_022 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_023 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_024 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_025 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_026 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_027 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_028 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_029 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_030 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_031 j)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
