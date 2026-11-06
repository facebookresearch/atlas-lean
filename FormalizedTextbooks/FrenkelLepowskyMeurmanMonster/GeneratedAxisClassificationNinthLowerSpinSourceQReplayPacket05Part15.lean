/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinPrimitivePackedReplayGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinLiteralQReplaySourcePacket05Part15
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinFastQMaskCentral

/-! Sixteen bounded chronological primitive steps, all full Q coordinate images. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_240 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 240 j := by
  change ∀ j : Fin 24, 240 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 240)
      (generatedNinthLowerSpinSourceQReplayWord 5 240 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 241 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_15 (0 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 240 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part15.getD 0 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_15_240,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_15_241, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_241 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 241 j := by
  change ∀ j : Fin 24, 241 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 241)
      (generatedNinthLowerSpinSourceQReplayWord 5 241 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 242 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_15 (1 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 241 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part15.getD 1 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_15_241,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_15_242, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_242 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 242 j := by
  change ∀ j : Fin 24, 242 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 242)
      (generatedNinthLowerSpinSourceQReplayWord 5 242 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 243 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_15 (2 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 242 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part15.getD 2 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_15_242,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_15_243, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_243 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 243 j := by
  change ∀ j : Fin 24, 243 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 243)
      (generatedNinthLowerSpinSourceQReplayWord 5 243 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 244 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_15 (3 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 243 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part15.getD 3 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_15_243,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_15_244, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_244 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 244 j := by
  change ∀ j : Fin 24, 244 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 244)
      (generatedNinthLowerSpinSourceQReplayWord 5 244 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 245 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_15 (4 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 244 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part15.getD 4 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_15_244,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_15_245, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_245 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 245 j := by
  change ∀ j : Fin 24, 245 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 245)
      (generatedNinthLowerSpinSourceQReplayWord 5 245 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 246 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_15 (5 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 245 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part15.getD 5 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_15_245,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_15_246, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_246 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 246 j := by
  change ∀ j : Fin 24, 246 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 246)
      (generatedNinthLowerSpinSourceQReplayWord 5 246 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 247 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_15 (6 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 246 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part15.getD 6 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_15_246,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_15_247, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_247 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 247 j := by
  change ∀ j : Fin 24, 247 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 247)
      (generatedNinthLowerSpinSourceQReplayWord 5 247 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 248 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_15 (7 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 247 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part15.getD 7 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_15_247,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_15_248, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_248 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 248 j := by
  change ∀ j : Fin 24, 248 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 248)
      (generatedNinthLowerSpinSourceQReplayWord 5 248 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 249 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_15 (8 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 248 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part15.getD 8 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_15_248,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_15_249, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_249 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 249 j := by
  change ∀ j : Fin 24, 249 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 249)
      (generatedNinthLowerSpinSourceQReplayWord 5 249 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 250 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_15 (9 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 249 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part15.getD 9 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_15_249,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_15_250, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_250 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 250 j := by
  change ∀ j : Fin 24, 250 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 250)
      (generatedNinthLowerSpinSourceQReplayWord 5 250 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 251 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_15 (10 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 250 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part15.getD 10 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_15_250,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_15_251, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_251 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 251 j := by
  change ∀ j : Fin 24, 251 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 251)
      (generatedNinthLowerSpinSourceQReplayWord 5 251 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 252 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_15 (11 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 251 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part15.getD 11 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_15_251,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_15_252, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_252 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 252 j := by
  change ∀ j : Fin 24, 252 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 252)
      (generatedNinthLowerSpinSourceQReplayWord 5 252 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 253 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_15 (12 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 252 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part15.getD 12 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_15_252,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_15_253, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_253 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 253 j := by
  change ∀ j : Fin 24, 253 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 253)
      (generatedNinthLowerSpinSourceQReplayWord 5 253 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 254 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_15 (13 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 253 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part15.getD 13 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_15_253,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_15_254, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_254 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 254 j := by
  change ∀ j : Fin 24, 254 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 254)
      (generatedNinthLowerSpinSourceQReplayWord 5 254 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 255 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_15 (14 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 254 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part15.getD 14 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_15_254,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_15_255, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_255 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 255 j := by
  change ∀ j : Fin 24, 255 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 255)
      (generatedNinthLowerSpinSourceQReplayWord 5 255 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 256 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_15 (15 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 255 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part15.getD 15 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_15_255,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_15_256, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

/-- Every actual primitive in this sixteen-step block retains all full central coordinates. -/
theorem generatedNinth_lower_spin_source_q_replay_packet_05_part_15 :
    ∀ n : Fin 16, ∀ j : Fin 24,
      240 + n.val < 314 →
        generatedNinthLowerSpinSourceQReplayStepCondition 5
          ⟨240 + n.val, by omega⟩ j := by
  intro n j hn
  fin_cases n
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_240 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_241 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_242 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_243 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_244 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_245 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_246 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_247 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_248 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_249 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_250 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_251 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_252 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_253 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_254 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_255 j)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
