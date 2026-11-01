/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinPrimitivePackedReplayGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinLiteralQReplaySourcePacket05Part17
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinFastQMaskCentral

/-! Sixteen bounded chronological primitive steps, all full Q coordinate images. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_272 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 272 j := by
  change ∀ j : Fin 24, 272 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 272)
      (generatedNinthLowerSpinSourceQReplayWord 5 272 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 273 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_17 (0 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 272 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part17.getD 0 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_17_272,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_17_273, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_273 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 273 j := by
  change ∀ j : Fin 24, 273 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 273)
      (generatedNinthLowerSpinSourceQReplayWord 5 273 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 274 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_17 (1 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 273 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part17.getD 1 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_17_273,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_17_274, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_274 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 274 j := by
  change ∀ j : Fin 24, 274 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 274)
      (generatedNinthLowerSpinSourceQReplayWord 5 274 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 275 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_17 (2 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 274 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part17.getD 2 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_17_274,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_17_275, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_275 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 275 j := by
  change ∀ j : Fin 24, 275 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 275)
      (generatedNinthLowerSpinSourceQReplayWord 5 275 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 276 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_17 (3 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 275 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part17.getD 3 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_17_275,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_17_276, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_276 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 276 j := by
  change ∀ j : Fin 24, 276 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 276)
      (generatedNinthLowerSpinSourceQReplayWord 5 276 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 277 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_17 (4 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 276 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part17.getD 4 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_17_276,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_17_277, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_277 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 277 j := by
  change ∀ j : Fin 24, 277 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 277)
      (generatedNinthLowerSpinSourceQReplayWord 5 277 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 278 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_17 (5 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 277 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part17.getD 5 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_17_277,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_17_278, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_278 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 278 j := by
  change ∀ j : Fin 24, 278 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 278)
      (generatedNinthLowerSpinSourceQReplayWord 5 278 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 279 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_17 (6 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 278 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part17.getD 6 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_17_278,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_17_279, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_279 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 279 j := by
  change ∀ j : Fin 24, 279 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 279)
      (generatedNinthLowerSpinSourceQReplayWord 5 279 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 280 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_17 (7 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 279 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part17.getD 7 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_17_279,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_17_280, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_280 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 280 j := by
  change ∀ j : Fin 24, 280 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 280)
      (generatedNinthLowerSpinSourceQReplayWord 5 280 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 281 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_17 (8 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 280 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part17.getD 8 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_17_280,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_17_281, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_281 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 281 j := by
  change ∀ j : Fin 24, 281 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 281)
      (generatedNinthLowerSpinSourceQReplayWord 5 281 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 282 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_17 (9 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 281 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part17.getD 9 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_17_281,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_17_282, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_282 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 282 j := by
  change ∀ j : Fin 24, 282 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 282)
      (generatedNinthLowerSpinSourceQReplayWord 5 282 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 283 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_17 (10 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 282 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part17.getD 10 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_17_282,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_17_283, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_283 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 283 j := by
  change ∀ j : Fin 24, 283 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 283)
      (generatedNinthLowerSpinSourceQReplayWord 5 283 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 284 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_17 (11 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 283 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part17.getD 11 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_17_283,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_17_284, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_284 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 284 j := by
  change ∀ j : Fin 24, 284 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 284)
      (generatedNinthLowerSpinSourceQReplayWord 5 284 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 285 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_17 (12 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 284 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part17.getD 12 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_17_284,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_17_285, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_285 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 285 j := by
  change ∀ j : Fin 24, 285 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 285)
      (generatedNinthLowerSpinSourceQReplayWord 5 285 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 286 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_17 (13 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 285 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part17.getD 13 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_17_285,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_17_286, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_286 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 286 j := by
  change ∀ j : Fin 24, 286 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 286)
      (generatedNinthLowerSpinSourceQReplayWord 5 286 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 287 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_17 (14 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 286 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part17.getD 14 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_17_286,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_17_287, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_287 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 287 j := by
  change ∀ j : Fin 24, 287 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 287)
      (generatedNinthLowerSpinSourceQReplayWord 5 287 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 288 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_17 (15 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 287 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part17.getD 15 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_17_287,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_17_288, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

/-- Every actual primitive in this sixteen-step block retains all full central coordinates. -/
theorem generatedNinth_lower_spin_source_q_replay_packet_05_part_17 :
    ∀ n : Fin 16, ∀ j : Fin 24,
      272 + n.val < 314 →
        generatedNinthLowerSpinSourceQReplayStepCondition 5
          ⟨272 + n.val, by omega⟩ j := by
  intro n j hn
  fin_cases n
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_272 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_273 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_274 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_275 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_276 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_277 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_278 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_279 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_280 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_281 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_282 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_283 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_284 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_285 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_286 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_287 j)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
