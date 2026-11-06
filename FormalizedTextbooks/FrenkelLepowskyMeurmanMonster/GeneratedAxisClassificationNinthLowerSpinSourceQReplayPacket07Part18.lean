/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinPrimitivePackedReplayGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinLiteralQReplaySourcePacket07Part18
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinFastQMaskCentral

/-! Sixteen bounded chronological primitive steps, all full Q coordinate images. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_288 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 288 j := by
  change ∀ j : Fin 24, 288 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 288)
      (generatedNinthLowerSpinSourceQReplayWord 7 288 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 289 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_18 (0 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 288 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part18.getD 0 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_18_288,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_18_289, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_289 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 289 j := by
  change ∀ j : Fin 24, 289 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 289)
      (generatedNinthLowerSpinSourceQReplayWord 7 289 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 290 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_18 (1 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 289 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part18.getD 1 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_18_289,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_18_290, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_290 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 290 j := by
  change ∀ j : Fin 24, 290 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 290)
      (generatedNinthLowerSpinSourceQReplayWord 7 290 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 291 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_18 (2 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 290 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part18.getD 2 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_18_290,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_18_291, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_291 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 291 j := by
  change ∀ j : Fin 24, 291 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 291)
      (generatedNinthLowerSpinSourceQReplayWord 7 291 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 292 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_18 (3 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 291 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part18.getD 3 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_18_291,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_18_292, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_292 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 292 j := by
  change ∀ j : Fin 24, 292 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 292)
      (generatedNinthLowerSpinSourceQReplayWord 7 292 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 293 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_18 (4 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 292 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part18.getD 4 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_18_292,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_18_293, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_293 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 293 j := by
  change ∀ j : Fin 24, 293 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 293)
      (generatedNinthLowerSpinSourceQReplayWord 7 293 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 294 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_18 (5 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 293 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part18.getD 5 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_18_293,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_18_294, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_294 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 294 j := by
  change ∀ j : Fin 24, 294 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 294)
      (generatedNinthLowerSpinSourceQReplayWord 7 294 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 295 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_18 (6 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 294 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part18.getD 6 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_18_294,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_18_295, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_295 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 295 j := by
  change ∀ j : Fin 24, 295 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 295)
      (generatedNinthLowerSpinSourceQReplayWord 7 295 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 296 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_18 (7 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 295 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part18.getD 7 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_18_295,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_18_296, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_296 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 296 j := by
  change ∀ j : Fin 24, 296 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 296)
      (generatedNinthLowerSpinSourceQReplayWord 7 296 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 297 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_18 (8 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 296 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part18.getD 8 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_18_296,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_18_297, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_297 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 297 j := by
  change ∀ j : Fin 24, 297 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 297)
      (generatedNinthLowerSpinSourceQReplayWord 7 297 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 298 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_18 (9 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 297 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part18.getD 9 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_18_297,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_18_298, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_298 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 298 j := by
  change ∀ j : Fin 24, 298 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 298)
      (generatedNinthLowerSpinSourceQReplayWord 7 298 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 299 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_18 (10 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 298 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part18.getD 10 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_18_298,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_18_299, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_299 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 299 j := by
  change ∀ j : Fin 24, 299 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 299)
      (generatedNinthLowerSpinSourceQReplayWord 7 299 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 300 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_18 (11 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 299 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part18.getD 11 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_18_299,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_18_300, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_300 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 300 j := by
  change ∀ j : Fin 24, 300 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 300)
      (generatedNinthLowerSpinSourceQReplayWord 7 300 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 301 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_18 (12 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 300 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part18.getD 12 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_18_300,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_18_301, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_301 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 301 j := by
  change ∀ j : Fin 24, 301 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 301)
      (generatedNinthLowerSpinSourceQReplayWord 7 301 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 302 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_18 (13 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 301 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part18.getD 13 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_18_301,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_18_302, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_302 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 302 j := by
  change ∀ j : Fin 24, 302 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 302)
      (generatedNinthLowerSpinSourceQReplayWord 7 302 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 303 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_18 (14 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 302 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part18.getD 14 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_18_302,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_18_303, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_303 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 303 j := by
  change ∀ j : Fin 24, 303 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 303)
      (generatedNinthLowerSpinSourceQReplayWord 7 303 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 304 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_18 (15 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 303 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part18.getD 15 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_18_303,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_18_304, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

/-- Every actual primitive in this sixteen-step block retains all full central coordinates. -/
theorem generatedNinth_lower_spin_source_q_replay_packet_07_part_18 :
    ∀ n : Fin 16, ∀ j : Fin 24,
      288 + n.val < 378 →
        generatedNinthLowerSpinSourceQReplayStepCondition 7
          ⟨288 + n.val, by omega⟩ j := by
  intro n j hn
  fin_cases n
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_288 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_289 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_290 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_291 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_292 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_293 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_294 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_295 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_296 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_297 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_298 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_299 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_300 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_301 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_302 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_303 j)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
