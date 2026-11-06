/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinPrimitivePackedReplayGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinLiteralQReplaySourcePacket07Part22
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinFastQMaskCentral

/-! Sixteen bounded chronological primitive steps, all full Q coordinate images. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_352 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 352 j := by
  change ∀ j : Fin 24, 352 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 352)
      (generatedNinthLowerSpinSourceQReplayWord 7 352 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 353 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_22 (0 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 352 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part22.getD 0 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_22_352,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_22_353, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_353 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 353 j := by
  change ∀ j : Fin 24, 353 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 353)
      (generatedNinthLowerSpinSourceQReplayWord 7 353 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 354 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_22 (1 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 353 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part22.getD 1 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_22_353,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_22_354, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_354 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 354 j := by
  change ∀ j : Fin 24, 354 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 354)
      (generatedNinthLowerSpinSourceQReplayWord 7 354 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 355 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_22 (2 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 354 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part22.getD 2 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_22_354,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_22_355, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_355 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 355 j := by
  change ∀ j : Fin 24, 355 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 355)
      (generatedNinthLowerSpinSourceQReplayWord 7 355 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 356 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_22 (3 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 355 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part22.getD 3 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_22_355,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_22_356, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_356 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 356 j := by
  change ∀ j : Fin 24, 356 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 356)
      (generatedNinthLowerSpinSourceQReplayWord 7 356 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 357 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_22 (4 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 356 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part22.getD 4 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_22_356,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_22_357, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_357 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 357 j := by
  change ∀ j : Fin 24, 357 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 357)
      (generatedNinthLowerSpinSourceQReplayWord 7 357 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 358 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_22 (5 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 357 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part22.getD 5 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_22_357,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_22_358, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_358 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 358 j := by
  change ∀ j : Fin 24, 358 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 358)
      (generatedNinthLowerSpinSourceQReplayWord 7 358 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 359 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_22 (6 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 358 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part22.getD 6 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_22_358,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_22_359, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_359 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 359 j := by
  change ∀ j : Fin 24, 359 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 359)
      (generatedNinthLowerSpinSourceQReplayWord 7 359 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 360 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_22 (7 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 359 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part22.getD 7 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_22_359,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_22_360, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_360 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 360 j := by
  change ∀ j : Fin 24, 360 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 360)
      (generatedNinthLowerSpinSourceQReplayWord 7 360 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 361 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_22 (8 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 360 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part22.getD 8 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_22_360,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_22_361, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_361 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 361 j := by
  change ∀ j : Fin 24, 361 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 361)
      (generatedNinthLowerSpinSourceQReplayWord 7 361 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 362 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_22 (9 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 361 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part22.getD 9 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_22_361,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_22_362, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_362 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 362 j := by
  change ∀ j : Fin 24, 362 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 362)
      (generatedNinthLowerSpinSourceQReplayWord 7 362 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 363 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_22 (10 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 362 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part22.getD 10 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_22_362,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_22_363, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_363 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 363 j := by
  change ∀ j : Fin 24, 363 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 363)
      (generatedNinthLowerSpinSourceQReplayWord 7 363 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 364 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_22 (11 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 363 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part22.getD 11 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_22_363,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_22_364, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_364 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 364 j := by
  change ∀ j : Fin 24, 364 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 364)
      (generatedNinthLowerSpinSourceQReplayWord 7 364 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 365 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_22 (12 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 364 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part22.getD 12 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_22_364,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_22_365, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_365 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 365 j := by
  change ∀ j : Fin 24, 365 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 365)
      (generatedNinthLowerSpinSourceQReplayWord 7 365 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 366 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_22 (13 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 365 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part22.getD 13 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_22_365,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_22_366, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_366 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 366 j := by
  change ∀ j : Fin 24, 366 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 366)
      (generatedNinthLowerSpinSourceQReplayWord 7 366 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 367 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_22 (14 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 366 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part22.getD 14 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_22_366,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_22_367, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_367 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 367 j := by
  change ∀ j : Fin 24, 367 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 367)
      (generatedNinthLowerSpinSourceQReplayWord 7 367 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 368 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_22 (15 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 367 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part22.getD 15 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_22_367,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_22_368, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

/-- Every actual primitive in this sixteen-step block retains all full central coordinates. -/
theorem generatedNinth_lower_spin_source_q_replay_packet_07_part_22 :
    ∀ n : Fin 16, ∀ j : Fin 24,
      352 + n.val < 378 →
        generatedNinthLowerSpinSourceQReplayStepCondition 7
          ⟨352 + n.val, by omega⟩ j := by
  intro n j hn
  fin_cases n
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_352 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_353 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_354 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_355 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_356 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_357 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_358 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_359 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_360 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_361 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_362 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_363 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_364 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_365 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_366 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_367 j)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
