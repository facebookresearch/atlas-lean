/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinPrimitivePackedReplayGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinLiteralQReplaySourcePacket07Part19
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinFastQMaskCentral

/-! Sixteen bounded chronological primitive steps, all full Q coordinate images. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_304 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 304 j := by
  change ∀ j : Fin 24, 304 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 304)
      (generatedNinthLowerSpinSourceQReplayWord 7 304 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 305 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_19 (0 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 304 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part19.getD 0 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_19_304,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_19_305, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_305 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 305 j := by
  change ∀ j : Fin 24, 305 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 305)
      (generatedNinthLowerSpinSourceQReplayWord 7 305 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 306 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_19 (1 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 305 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part19.getD 1 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_19_305,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_19_306, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_306 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 306 j := by
  change ∀ j : Fin 24, 306 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 306)
      (generatedNinthLowerSpinSourceQReplayWord 7 306 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 307 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_19 (2 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 306 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part19.getD 2 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_19_306,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_19_307, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_307 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 307 j := by
  change ∀ j : Fin 24, 307 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 307)
      (generatedNinthLowerSpinSourceQReplayWord 7 307 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 308 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_19 (3 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 307 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part19.getD 3 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_19_307,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_19_308, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_308 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 308 j := by
  change ∀ j : Fin 24, 308 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 308)
      (generatedNinthLowerSpinSourceQReplayWord 7 308 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 309 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_19 (4 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 308 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part19.getD 4 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_19_308,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_19_309, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_309 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 309 j := by
  change ∀ j : Fin 24, 309 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 309)
      (generatedNinthLowerSpinSourceQReplayWord 7 309 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 310 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_19 (5 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 309 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part19.getD 5 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_19_309,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_19_310, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_310 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 310 j := by
  change ∀ j : Fin 24, 310 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 310)
      (generatedNinthLowerSpinSourceQReplayWord 7 310 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 311 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_19 (6 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 310 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part19.getD 6 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_19_310,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_19_311, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_311 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 311 j := by
  change ∀ j : Fin 24, 311 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 311)
      (generatedNinthLowerSpinSourceQReplayWord 7 311 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 312 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_19 (7 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 311 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part19.getD 7 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_19_311,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_19_312, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_312 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 312 j := by
  change ∀ j : Fin 24, 312 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 312)
      (generatedNinthLowerSpinSourceQReplayWord 7 312 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 313 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_19 (8 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 312 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part19.getD 8 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_19_312,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_19_313, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_313 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 313 j := by
  change ∀ j : Fin 24, 313 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 313)
      (generatedNinthLowerSpinSourceQReplayWord 7 313 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 314 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_19 (9 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 313 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part19.getD 9 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_19_313,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_19_314, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_314 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 314 j := by
  change ∀ j : Fin 24, 314 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 314)
      (generatedNinthLowerSpinSourceQReplayWord 7 314 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 315 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_19 (10 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 314 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part19.getD 10 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_19_314,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_19_315, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_315 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 315 j := by
  change ∀ j : Fin 24, 315 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 315)
      (generatedNinthLowerSpinSourceQReplayWord 7 315 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 316 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_19 (11 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 315 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part19.getD 11 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_19_315,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_19_316, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_316 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 316 j := by
  change ∀ j : Fin 24, 316 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 316)
      (generatedNinthLowerSpinSourceQReplayWord 7 316 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 317 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_19 (12 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 316 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part19.getD 12 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_19_316,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_19_317, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_317 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 317 j := by
  change ∀ j : Fin 24, 317 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 317)
      (generatedNinthLowerSpinSourceQReplayWord 7 317 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 318 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_19 (13 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 317 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part19.getD 13 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_19_317,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_19_318, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_318 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 318 j := by
  change ∀ j : Fin 24, 318 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 318)
      (generatedNinthLowerSpinSourceQReplayWord 7 318 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 319 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_19 (14 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 318 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part19.getD 14 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_19_318,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_19_319, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_319 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 319 j := by
  change ∀ j : Fin 24, 319 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 319)
      (generatedNinthLowerSpinSourceQReplayWord 7 319 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 320 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_19 (15 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 319 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part19.getD 15 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_19_319,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_19_320, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

/-- Every actual primitive in this sixteen-step block retains all full central coordinates. -/
theorem generatedNinth_lower_spin_source_q_replay_packet_07_part_19 :
    ∀ n : Fin 16, ∀ j : Fin 24,
      304 + n.val < 378 →
        generatedNinthLowerSpinSourceQReplayStepCondition 7
          ⟨304 + n.val, by omega⟩ j := by
  intro n j hn
  fin_cases n
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_304 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_305 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_306 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_307 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_308 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_309 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_310 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_311 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_312 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_313 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_314 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_315 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_316 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_317 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_318 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_319 j)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
