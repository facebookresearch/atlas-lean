/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinPrimitivePackedReplayGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinLiteralQReplaySourcePacket07Part20
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinFastQMaskCentral

/-! Sixteen bounded chronological primitive steps, all full Q coordinate images. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_320 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 320 j := by
  change ∀ j : Fin 24, 320 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 320)
      (generatedNinthLowerSpinSourceQReplayWord 7 320 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 321 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_20 (0 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 320 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part20.getD 0 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_20_320,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_20_321, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_321 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 321 j := by
  change ∀ j : Fin 24, 321 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 321)
      (generatedNinthLowerSpinSourceQReplayWord 7 321 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 322 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_20 (1 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 321 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part20.getD 1 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_20_321,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_20_322, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_322 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 322 j := by
  change ∀ j : Fin 24, 322 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 322)
      (generatedNinthLowerSpinSourceQReplayWord 7 322 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 323 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_20 (2 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 322 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part20.getD 2 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_20_322,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_20_323, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_323 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 323 j := by
  change ∀ j : Fin 24, 323 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 323)
      (generatedNinthLowerSpinSourceQReplayWord 7 323 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 324 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_20 (3 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 323 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part20.getD 3 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_20_323,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_20_324, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_324 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 324 j := by
  change ∀ j : Fin 24, 324 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 324)
      (generatedNinthLowerSpinSourceQReplayWord 7 324 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 325 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_20 (4 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 324 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part20.getD 4 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_20_324,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_20_325, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_325 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 325 j := by
  change ∀ j : Fin 24, 325 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 325)
      (generatedNinthLowerSpinSourceQReplayWord 7 325 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 326 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_20 (5 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 325 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part20.getD 5 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_20_325,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_20_326, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_326 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 326 j := by
  change ∀ j : Fin 24, 326 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 326)
      (generatedNinthLowerSpinSourceQReplayWord 7 326 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 327 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_20 (6 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 326 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part20.getD 6 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_20_326,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_20_327, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_327 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 327 j := by
  change ∀ j : Fin 24, 327 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 327)
      (generatedNinthLowerSpinSourceQReplayWord 7 327 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 328 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_20 (7 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 327 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part20.getD 7 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_20_327,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_20_328, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_328 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 328 j := by
  change ∀ j : Fin 24, 328 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 328)
      (generatedNinthLowerSpinSourceQReplayWord 7 328 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 329 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_20 (8 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 328 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part20.getD 8 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_20_328,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_20_329, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_329 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 329 j := by
  change ∀ j : Fin 24, 329 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 329)
      (generatedNinthLowerSpinSourceQReplayWord 7 329 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 330 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_20 (9 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 329 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part20.getD 9 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_20_329,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_20_330, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_330 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 330 j := by
  change ∀ j : Fin 24, 330 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 330)
      (generatedNinthLowerSpinSourceQReplayWord 7 330 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 331 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_20 (10 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 330 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part20.getD 10 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_20_330,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_20_331, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_331 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 331 j := by
  change ∀ j : Fin 24, 331 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 331)
      (generatedNinthLowerSpinSourceQReplayWord 7 331 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 332 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_20 (11 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 331 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part20.getD 11 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_20_331,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_20_332, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_332 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 332 j := by
  change ∀ j : Fin 24, 332 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 332)
      (generatedNinthLowerSpinSourceQReplayWord 7 332 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 333 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_20 (12 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 332 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part20.getD 12 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_20_332,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_20_333, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_333 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 333 j := by
  change ∀ j : Fin 24, 333 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 333)
      (generatedNinthLowerSpinSourceQReplayWord 7 333 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 334 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_20 (13 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 333 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part20.getD 13 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_20_333,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_20_334, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_334 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 334 j := by
  change ∀ j : Fin 24, 334 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 334)
      (generatedNinthLowerSpinSourceQReplayWord 7 334 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 335 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_20 (14 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 334 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part20.getD 14 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_20_334,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_20_335, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_335 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 335 j := by
  change ∀ j : Fin 24, 335 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 335)
      (generatedNinthLowerSpinSourceQReplayWord 7 335 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 336 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_20 (15 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 335 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part20.getD 15 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_20_335,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_20_336, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

/-- Every actual primitive in this sixteen-step block retains all full central coordinates. -/
theorem generatedNinth_lower_spin_source_q_replay_packet_07_part_20 :
    ∀ n : Fin 16, ∀ j : Fin 24,
      320 + n.val < 378 →
        generatedNinthLowerSpinSourceQReplayStepCondition 7
          ⟨320 + n.val, by omega⟩ j := by
  intro n j hn
  fin_cases n
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_320 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_321 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_322 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_323 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_324 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_325 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_326 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_327 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_328 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_329 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_330 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_331 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_332 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_333 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_334 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_335 j)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
