/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinPrimitivePackedReplayGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinLiteralQReplaySourcePacket07Part13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinFastQMaskCentral

/-! Sixteen bounded chronological primitive steps, all full Q coordinate images. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_208 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 208 j := by
  change ∀ j : Fin 24, 208 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 208)
      (generatedNinthLowerSpinSourceQReplayWord 7 208 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 209 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_13 (0 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 208 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part13.getD 0 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_13_208,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_13_209, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_209 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 209 j := by
  change ∀ j : Fin 24, 209 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 209)
      (generatedNinthLowerSpinSourceQReplayWord 7 209 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 210 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_13 (1 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 209 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part13.getD 1 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_13_209,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_13_210, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_210 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 210 j := by
  change ∀ j : Fin 24, 210 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 210)
      (generatedNinthLowerSpinSourceQReplayWord 7 210 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 211 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_13 (2 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 210 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part13.getD 2 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_13_210,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_13_211, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_211 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 211 j := by
  change ∀ j : Fin 24, 211 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 211)
      (generatedNinthLowerSpinSourceQReplayWord 7 211 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 212 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_13 (3 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 211 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part13.getD 3 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_13_211,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_13_212, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_212 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 212 j := by
  change ∀ j : Fin 24, 212 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 212)
      (generatedNinthLowerSpinSourceQReplayWord 7 212 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 213 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_13 (4 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 212 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part13.getD 4 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_13_212,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_13_213, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_213 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 213 j := by
  change ∀ j : Fin 24, 213 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 213)
      (generatedNinthLowerSpinSourceQReplayWord 7 213 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 214 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_13 (5 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 213 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part13.getD 5 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_13_213,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_13_214, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_214 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 214 j := by
  change ∀ j : Fin 24, 214 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 214)
      (generatedNinthLowerSpinSourceQReplayWord 7 214 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 215 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_13 (6 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 214 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part13.getD 6 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_13_214,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_13_215, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_215 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 215 j := by
  change ∀ j : Fin 24, 215 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 215)
      (generatedNinthLowerSpinSourceQReplayWord 7 215 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 216 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_13 (7 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 215 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part13.getD 7 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_13_215,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_13_216, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_216 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 216 j := by
  change ∀ j : Fin 24, 216 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 216)
      (generatedNinthLowerSpinSourceQReplayWord 7 216 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 217 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_13 (8 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 216 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part13.getD 8 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_13_216,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_13_217, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_217 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 217 j := by
  change ∀ j : Fin 24, 217 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 217)
      (generatedNinthLowerSpinSourceQReplayWord 7 217 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 218 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_13 (9 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 217 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part13.getD 9 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_13_217,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_13_218, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_218 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 218 j := by
  change ∀ j : Fin 24, 218 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 218)
      (generatedNinthLowerSpinSourceQReplayWord 7 218 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 219 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_13 (10 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 218 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part13.getD 10 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_13_218,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_13_219, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_219 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 219 j := by
  change ∀ j : Fin 24, 219 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 219)
      (generatedNinthLowerSpinSourceQReplayWord 7 219 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 220 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_13 (11 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 219 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part13.getD 11 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_13_219,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_13_220, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_220 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 220 j := by
  change ∀ j : Fin 24, 220 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 220)
      (generatedNinthLowerSpinSourceQReplayWord 7 220 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 221 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_13 (12 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 220 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part13.getD 12 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_13_220,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_13_221, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_221 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 221 j := by
  change ∀ j : Fin 24, 221 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 221)
      (generatedNinthLowerSpinSourceQReplayWord 7 221 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 222 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_13 (13 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 221 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part13.getD 13 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_13_221,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_13_222, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_222 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 222 j := by
  change ∀ j : Fin 24, 222 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 222)
      (generatedNinthLowerSpinSourceQReplayWord 7 222 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 223 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_13 (14 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 222 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part13.getD 14 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_13_222,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_13_223, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_223 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 7 223 j := by
  change ∀ j : Fin 24, 223 < (generatedNinthLowerSpinSourceWord 7).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 7 223)
      (generatedNinthLowerSpinSourceQReplayWord 7 223 j)
      (generatedNinthLowerSpinSourceQReplayWord 7 224 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_07_part_13 (15 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 7 223 =
    generatedNinthLowerSpinLiteralQReplayLetters07Part13.getD 15 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_07_part_13_223,
    generatedNinth_lower_spin_literal_q_replay_prefix_07_part_13_224, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

/-- Every actual primitive in this sixteen-step block retains all full central coordinates. -/
theorem generatedNinth_lower_spin_source_q_replay_packet_07_part_13 :
    ∀ n : Fin 16, ∀ j : Fin 24,
      208 + n.val < 378 →
        generatedNinthLowerSpinSourceQReplayStepCondition 7
          ⟨208 + n.val, by omega⟩ j := by
  intro n j hn
  fin_cases n
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_208 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_209 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_210 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_211 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_212 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_213 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_214 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_215 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_216 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_217 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_218 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_219 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_220 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_221 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_222 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_223 j)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
