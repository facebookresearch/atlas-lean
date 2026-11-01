/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinPrimitivePackedReplayGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinLiteralQReplaySourcePacket07Part16
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinFastQMaskCentral

/-! Sixteen bounded chronological primitive steps, all full Q coordinate images. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_256 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 256 j := by
  change ∀ j : Fin 24, 256 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 256)
      (generatedNinthLowerSpinSourceQReplayWord 7 256 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 257 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_16 (0 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 256 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part16.getD 0 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_16_256,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_16_257, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_257 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 257 j := by
  change ∀ j : Fin 24, 257 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 257)
      (generatedNinthLowerSpinSourceQReplayWord 7 257 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 258 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_16 (1 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 257 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part16.getD 1 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_16_257,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_16_258, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_258 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 258 j := by
  change ∀ j : Fin 24, 258 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 258)
      (generatedNinthLowerSpinSourceQReplayWord 7 258 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 259 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_16 (2 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 258 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part16.getD 2 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_16_258,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_16_259, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_259 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 259 j := by
  change ∀ j : Fin 24, 259 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 259)
      (generatedNinthLowerSpinSourceQReplayWord 7 259 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 260 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_16 (3 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 259 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part16.getD 3 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_16_259,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_16_260, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_260 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 260 j := by
  change ∀ j : Fin 24, 260 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 260)
      (generatedNinthLowerSpinSourceQReplayWord 7 260 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 261 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_16 (4 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 260 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part16.getD 4 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_16_260,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_16_261, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_261 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 261 j := by
  change ∀ j : Fin 24, 261 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 261)
      (generatedNinthLowerSpinSourceQReplayWord 7 261 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 262 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_16 (5 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 261 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part16.getD 5 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_16_261,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_16_262, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_262 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 262 j := by
  change ∀ j : Fin 24, 262 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 262)
      (generatedNinthLowerSpinSourceQReplayWord 7 262 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 263 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_16 (6 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 262 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part16.getD 6 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_16_262,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_16_263, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_263 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 263 j := by
  change ∀ j : Fin 24, 263 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 263)
      (generatedNinthLowerSpinSourceQReplayWord 7 263 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 264 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_16 (7 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 263 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part16.getD 7 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_16_263,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_16_264, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_264 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 264 j := by
  change ∀ j : Fin 24, 264 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 264)
      (generatedNinthLowerSpinSourceQReplayWord 7 264 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 265 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_16 (8 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 264 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part16.getD 8 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_16_264,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_16_265, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_265 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 265 j := by
  change ∀ j : Fin 24, 265 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 265)
      (generatedNinthLowerSpinSourceQReplayWord 7 265 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 266 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_16 (9 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 265 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part16.getD 9 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_16_265,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_16_266, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_266 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 266 j := by
  change ∀ j : Fin 24, 266 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 266)
      (generatedNinthLowerSpinSourceQReplayWord 7 266 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 267 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_16 (10 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 266 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part16.getD 10 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_16_266,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_16_267, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_267 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 267 j := by
  change ∀ j : Fin 24, 267 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 267)
      (generatedNinthLowerSpinSourceQReplayWord 7 267 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 268 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_16 (11 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 267 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part16.getD 11 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_16_267,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_16_268, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_268 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 268 j := by
  change ∀ j : Fin 24, 268 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 268)
      (generatedNinthLowerSpinSourceQReplayWord 7 268 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 269 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_16 (12 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 268 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part16.getD 12 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_16_268,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_16_269, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_269 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 269 j := by
  change ∀ j : Fin 24, 269 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 269)
      (generatedNinthLowerSpinSourceQReplayWord 7 269 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 270 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_16 (13 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 269 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part16.getD 13 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_16_269,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_16_270, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_270 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 270 j := by
  change ∀ j : Fin 24, 270 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 270)
      (generatedNinthLowerSpinSourceQReplayWord 7 270 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 271 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_16 (14 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 270 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part16.getD 14 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_16_270,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_16_271, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_271 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 271 j := by
  change ∀ j : Fin 24, 271 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 271)
      (generatedNinthLowerSpinSourceQReplayWord 7 271 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 272 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_16 (15 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 271 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part16.getD 15 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_16_271,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_16_272, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

/-- Every actual primitive in this sixteen-step block retains all full central coordinates. -/
theorem generatedNinth_lower_spin_source_q_replay_packet_07_part_16 :
    ∀ n : Fin 16, ∀ j : Fin 24,
      256 + n.val < 378 →
        generatedNinthLowerSpinSourceQReplayStepCondition 7
          ⟨256 + n.val, by omega⟩ j := by
  intro n j hn
  fin_cases n
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_256 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_257 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_258 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_259 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_260 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_261 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_262 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_263 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_264 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_265 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_266 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_267 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_268 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_269 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_270 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_271 j)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
