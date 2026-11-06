/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinPrimitivePackedReplayGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinLiteralQReplaySourcePacket05Part14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinFastQMaskCentral

/-! Sixteen bounded chronological primitive steps, all full Q coordinate images. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_224 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 224 j := by
  change ∀ j : Fin 24, 224 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 224)
      (generatedNinthLowerSpinSourceQReplayWord 5 224 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 225 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_14 (0 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 224 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part14.getD 0 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_14_224,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_14_225, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_225 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 225 j := by
  change ∀ j : Fin 24, 225 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 225)
      (generatedNinthLowerSpinSourceQReplayWord 5 225 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 226 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_14 (1 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 225 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part14.getD 1 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_14_225,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_14_226, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_226 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 226 j := by
  change ∀ j : Fin 24, 226 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 226)
      (generatedNinthLowerSpinSourceQReplayWord 5 226 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 227 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_14 (2 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 226 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part14.getD 2 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_14_226,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_14_227, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_227 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 227 j := by
  change ∀ j : Fin 24, 227 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 227)
      (generatedNinthLowerSpinSourceQReplayWord 5 227 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 228 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_14 (3 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 227 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part14.getD 3 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_14_227,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_14_228, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_228 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 228 j := by
  change ∀ j : Fin 24, 228 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 228)
      (generatedNinthLowerSpinSourceQReplayWord 5 228 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 229 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_14 (4 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 228 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part14.getD 4 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_14_228,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_14_229, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_229 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 229 j := by
  change ∀ j : Fin 24, 229 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 229)
      (generatedNinthLowerSpinSourceQReplayWord 5 229 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 230 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_14 (5 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 229 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part14.getD 5 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_14_229,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_14_230, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_230 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 230 j := by
  change ∀ j : Fin 24, 230 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 230)
      (generatedNinthLowerSpinSourceQReplayWord 5 230 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 231 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_14 (6 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 230 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part14.getD 6 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_14_230,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_14_231, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_231 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 231 j := by
  change ∀ j : Fin 24, 231 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 231)
      (generatedNinthLowerSpinSourceQReplayWord 5 231 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 232 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_14 (7 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 231 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part14.getD 7 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_14_231,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_14_232, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_232 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 232 j := by
  change ∀ j : Fin 24, 232 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 232)
      (generatedNinthLowerSpinSourceQReplayWord 5 232 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 233 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_14 (8 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 232 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part14.getD 8 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_14_232,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_14_233, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_233 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 233 j := by
  change ∀ j : Fin 24, 233 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 233)
      (generatedNinthLowerSpinSourceQReplayWord 5 233 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 234 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_14 (9 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 233 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part14.getD 9 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_14_233,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_14_234, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_234 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 234 j := by
  change ∀ j : Fin 24, 234 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 234)
      (generatedNinthLowerSpinSourceQReplayWord 5 234 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 235 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_14 (10 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 234 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part14.getD 10 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_14_234,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_14_235, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_235 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 235 j := by
  change ∀ j : Fin 24, 235 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 235)
      (generatedNinthLowerSpinSourceQReplayWord 5 235 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 236 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_14 (11 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 235 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part14.getD 11 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_14_235,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_14_236, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_236 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 236 j := by
  change ∀ j : Fin 24, 236 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 236)
      (generatedNinthLowerSpinSourceQReplayWord 5 236 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 237 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_14 (12 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 236 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part14.getD 12 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_14_236,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_14_237, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_237 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 237 j := by
  change ∀ j : Fin 24, 237 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 237)
      (generatedNinthLowerSpinSourceQReplayWord 5 237 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 238 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_14 (13 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 237 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part14.getD 13 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_14_237,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_14_238, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_238 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 238 j := by
  change ∀ j : Fin 24, 238 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 238)
      (generatedNinthLowerSpinSourceQReplayWord 5 238 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 239 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_14 (14 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 238 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part14.getD 14 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_14_238,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_14_239, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_239 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 239 j := by
  change ∀ j : Fin 24, 239 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 239)
      (generatedNinthLowerSpinSourceQReplayWord 5 239 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 240 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_14 (15 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 239 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part14.getD 15 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_14_239,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_14_240, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

/-- Every actual primitive in this sixteen-step block retains all full central coordinates. -/
theorem generatedNinth_lower_spin_source_q_replay_packet_05_part_14 :
    ∀ n : Fin 16, ∀ j : Fin 24,
      224 + n.val < 314 →
        generatedNinthLowerSpinSourceQReplayStepCondition 5
          ⟨224 + n.val, by omega⟩ j := by
  intro n j hn
  fin_cases n
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_224 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_225 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_226 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_227 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_228 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_229 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_230 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_231 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_232 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_233 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_234 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_235 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_236 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_237 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_238 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_239 j)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
