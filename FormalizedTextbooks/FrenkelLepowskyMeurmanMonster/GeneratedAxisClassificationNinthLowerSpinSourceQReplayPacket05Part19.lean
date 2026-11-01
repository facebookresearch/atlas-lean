/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinPrimitivePackedReplayGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinLiteralQReplaySourcePacket05Part19
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinFastQMaskCentral

/-! Sixteen bounded chronological primitive steps, all full Q coordinate images. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_304 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 304 j := by
  change ∀ j : Fin 24, 304 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 304)
      (generatedNinthLowerSpinSourceQReplayWord 5 304 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 305 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_19 (0 : Fin 10)
  change generatedNinthLowerSpinSourceQReplayLetter 5 304 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part19.getD 0 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_19_304,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_19_305, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_305 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 305 j := by
  change ∀ j : Fin 24, 305 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 305)
      (generatedNinthLowerSpinSourceQReplayWord 5 305 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 306 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_19 (1 : Fin 10)
  change generatedNinthLowerSpinSourceQReplayLetter 5 305 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part19.getD 1 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_19_305,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_19_306, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_306 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 306 j := by
  change ∀ j : Fin 24, 306 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 306)
      (generatedNinthLowerSpinSourceQReplayWord 5 306 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 307 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_19 (2 : Fin 10)
  change generatedNinthLowerSpinSourceQReplayLetter 5 306 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part19.getD 2 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_19_306,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_19_307, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_307 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 307 j := by
  change ∀ j : Fin 24, 307 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 307)
      (generatedNinthLowerSpinSourceQReplayWord 5 307 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 308 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_19 (3 : Fin 10)
  change generatedNinthLowerSpinSourceQReplayLetter 5 307 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part19.getD 3 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_19_307,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_19_308, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_308 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 308 j := by
  change ∀ j : Fin 24, 308 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 308)
      (generatedNinthLowerSpinSourceQReplayWord 5 308 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 309 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_19 (4 : Fin 10)
  change generatedNinthLowerSpinSourceQReplayLetter 5 308 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part19.getD 4 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_19_308,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_19_309, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_309 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 309 j := by
  change ∀ j : Fin 24, 309 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 309)
      (generatedNinthLowerSpinSourceQReplayWord 5 309 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 310 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_19 (5 : Fin 10)
  change generatedNinthLowerSpinSourceQReplayLetter 5 309 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part19.getD 5 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_19_309,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_19_310, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_310 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 310 j := by
  change ∀ j : Fin 24, 310 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 310)
      (generatedNinthLowerSpinSourceQReplayWord 5 310 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 311 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_19 (6 : Fin 10)
  change generatedNinthLowerSpinSourceQReplayLetter 5 310 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part19.getD 6 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_19_310,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_19_311, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_311 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 311 j := by
  change ∀ j : Fin 24, 311 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 311)
      (generatedNinthLowerSpinSourceQReplayWord 5 311 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 312 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_19 (7 : Fin 10)
  change generatedNinthLowerSpinSourceQReplayLetter 5 311 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part19.getD 7 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_19_311,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_19_312, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_312 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 312 j := by
  change ∀ j : Fin 24, 312 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 312)
      (generatedNinthLowerSpinSourceQReplayWord 5 312 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 313 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_19 (8 : Fin 10)
  change generatedNinthLowerSpinSourceQReplayLetter 5 312 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part19.getD 8 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_19_312,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_19_313, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_313 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 313 j := by
  change ∀ j : Fin 24, 313 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 313)
      (generatedNinthLowerSpinSourceQReplayWord 5 313 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 314 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_19 (9 : Fin 10)
  change generatedNinthLowerSpinSourceQReplayLetter 5 313 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part19.getD 9 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_19_313,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_19_314, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

/-- Every actual primitive in this sixteen-step block retains all full central coordinates. -/
theorem generatedNinth_lower_spin_source_q_replay_packet_05_part_19 :
    ∀ n : Fin 16, ∀ j : Fin 24,
      304 + n.val < 314 →
        generatedNinthLowerSpinSourceQReplayStepCondition 5
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
  · norm_num at hn
  · norm_num at hn
  · norm_num at hn
  · norm_num at hn
  · norm_num at hn
  · norm_num at hn

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
