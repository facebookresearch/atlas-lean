/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinPrimitivePackedReplayGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinLiteralQReplaySourcePacket04Part09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinFastQMaskCentral

/-! Sixteen bounded chronological primitive steps, all full Q coordinate images. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_144 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 144 j := by
  change ∀ j : Fin 24, 144 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 144)
      (generatedNinthLowerSpinSourceQReplayWord 4 144 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 145 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_09 (0 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 144 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part09.getD 0 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_09_144,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_09_145, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_145 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 145 j := by
  change ∀ j : Fin 24, 145 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 145)
      (generatedNinthLowerSpinSourceQReplayWord 4 145 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 146 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_09 (1 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 145 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part09.getD 1 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_09_145,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_09_146, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_146 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 146 j := by
  change ∀ j : Fin 24, 146 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 146)
      (generatedNinthLowerSpinSourceQReplayWord 4 146 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 147 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_09 (2 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 146 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part09.getD 2 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_09_146,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_09_147, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_147 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 147 j := by
  change ∀ j : Fin 24, 147 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 147)
      (generatedNinthLowerSpinSourceQReplayWord 4 147 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 148 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_09 (3 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 147 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part09.getD 3 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_09_147,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_09_148, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_148 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 148 j := by
  change ∀ j : Fin 24, 148 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 148)
      (generatedNinthLowerSpinSourceQReplayWord 4 148 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 149 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_09 (4 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 148 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part09.getD 4 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_09_148,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_09_149, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_149 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 149 j := by
  change ∀ j : Fin 24, 149 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 149)
      (generatedNinthLowerSpinSourceQReplayWord 4 149 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 150 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_09 (5 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 149 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part09.getD 5 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_09_149,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_09_150, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_150 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 150 j := by
  change ∀ j : Fin 24, 150 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 150)
      (generatedNinthLowerSpinSourceQReplayWord 4 150 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 151 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_09 (6 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 150 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part09.getD 6 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_09_150,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_09_151, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_151 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 151 j := by
  change ∀ j : Fin 24, 151 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 151)
      (generatedNinthLowerSpinSourceQReplayWord 4 151 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 152 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_09 (7 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 151 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part09.getD 7 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_09_151,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_09_152, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_152 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 152 j := by
  change ∀ j : Fin 24, 152 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 152)
      (generatedNinthLowerSpinSourceQReplayWord 4 152 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 153 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_09 (8 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 152 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part09.getD 8 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_09_152,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_09_153, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_153 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 153 j := by
  change ∀ j : Fin 24, 153 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 153)
      (generatedNinthLowerSpinSourceQReplayWord 4 153 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 154 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_09 (9 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 153 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part09.getD 9 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_09_153,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_09_154, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_154 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 154 j := by
  change ∀ j : Fin 24, 154 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 154)
      (generatedNinthLowerSpinSourceQReplayWord 4 154 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 155 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_09 (10 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 154 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part09.getD 10 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_09_154,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_09_155, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_155 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 155 j := by
  change ∀ j : Fin 24, 155 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 155)
      (generatedNinthLowerSpinSourceQReplayWord 4 155 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 156 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_09 (11 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 155 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part09.getD 11 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_09_155,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_09_156, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_156 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 156 j := by
  change ∀ j : Fin 24, 156 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 156)
      (generatedNinthLowerSpinSourceQReplayWord 4 156 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 157 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_09 (12 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 156 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part09.getD 12 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_09_156,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_09_157, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_157 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 157 j := by
  change ∀ j : Fin 24, 157 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 157)
      (generatedNinthLowerSpinSourceQReplayWord 4 157 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 158 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_09 (13 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 157 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part09.getD 13 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_09_157,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_09_158, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_158 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 158 j := by
  change ∀ j : Fin 24, 158 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 158)
      (generatedNinthLowerSpinSourceQReplayWord 4 158 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 159 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_09 (14 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 158 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part09.getD 14 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_09_158,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_09_159, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_159 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 159 j := by
  change ∀ j : Fin 24, 159 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 159)
      (generatedNinthLowerSpinSourceQReplayWord 4 159 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 160 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_09 (15 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 159 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part09.getD 15 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_09_159,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_09_160, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

/-- Every actual primitive in this sixteen-step block retains all full central coordinates. -/
theorem generatedNinth_lower_spin_source_q_replay_packet_04_part_09 :
    ∀ n : Fin 16, ∀ j : Fin 24,
      144 + n.val < 175 →
        generatedNinthLowerSpinSourceQReplayStepCondition 4
          ⟨144 + n.val, by omega⟩ j := by
  intro n j hn
  fin_cases n
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_144 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_145 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_146 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_147 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_148 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_149 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_150 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_151 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_152 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_153 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_154 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_155 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_156 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_157 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_158 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_159 j)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
