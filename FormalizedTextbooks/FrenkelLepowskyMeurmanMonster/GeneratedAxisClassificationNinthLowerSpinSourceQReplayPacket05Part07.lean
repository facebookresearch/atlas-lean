/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinPrimitivePackedReplayGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinLiteralQReplaySourcePacket05Part07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinFastQMaskCentral

/-! Sixteen bounded chronological primitive steps, all full Q coordinate images. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_112 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 112 j := by
  change ∀ j : Fin 24, 112 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 112)
      (generatedNinthLowerSpinSourceQReplayWord 5 112 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 113 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_07 (0 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 112 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part07.getD 0 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_07_112,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_07_113, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_113 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 113 j := by
  change ∀ j : Fin 24, 113 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 113)
      (generatedNinthLowerSpinSourceQReplayWord 5 113 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 114 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_07 (1 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 113 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part07.getD 1 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_07_113,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_07_114, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_114 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 114 j := by
  change ∀ j : Fin 24, 114 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 114)
      (generatedNinthLowerSpinSourceQReplayWord 5 114 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 115 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_07 (2 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 114 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part07.getD 2 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_07_114,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_07_115, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_115 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 115 j := by
  change ∀ j : Fin 24, 115 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 115)
      (generatedNinthLowerSpinSourceQReplayWord 5 115 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 116 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_07 (3 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 115 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part07.getD 3 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_07_115,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_07_116, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_116 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 116 j := by
  change ∀ j : Fin 24, 116 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 116)
      (generatedNinthLowerSpinSourceQReplayWord 5 116 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 117 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_07 (4 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 116 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part07.getD 4 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_07_116,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_07_117, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_117 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 117 j := by
  change ∀ j : Fin 24, 117 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 117)
      (generatedNinthLowerSpinSourceQReplayWord 5 117 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 118 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_07 (5 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 117 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part07.getD 5 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_07_117,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_07_118, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_118 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 118 j := by
  change ∀ j : Fin 24, 118 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 118)
      (generatedNinthLowerSpinSourceQReplayWord 5 118 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 119 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_07 (6 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 118 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part07.getD 6 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_07_118,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_07_119, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_119 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 119 j := by
  change ∀ j : Fin 24, 119 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 119)
      (generatedNinthLowerSpinSourceQReplayWord 5 119 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 120 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_07 (7 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 119 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part07.getD 7 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_07_119,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_07_120, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_120 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 120 j := by
  change ∀ j : Fin 24, 120 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 120)
      (generatedNinthLowerSpinSourceQReplayWord 5 120 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 121 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_07 (8 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 120 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part07.getD 8 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_07_120,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_07_121, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_121 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 121 j := by
  change ∀ j : Fin 24, 121 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 121)
      (generatedNinthLowerSpinSourceQReplayWord 5 121 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 122 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_07 (9 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 121 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part07.getD 9 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_07_121,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_07_122, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_122 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 122 j := by
  change ∀ j : Fin 24, 122 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 122)
      (generatedNinthLowerSpinSourceQReplayWord 5 122 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 123 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_07 (10 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 122 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part07.getD 10 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_07_122,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_07_123, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_123 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 123 j := by
  change ∀ j : Fin 24, 123 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 123)
      (generatedNinthLowerSpinSourceQReplayWord 5 123 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 124 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_07 (11 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 123 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part07.getD 11 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_07_123,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_07_124, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_124 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 124 j := by
  change ∀ j : Fin 24, 124 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 124)
      (generatedNinthLowerSpinSourceQReplayWord 5 124 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 125 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_07 (12 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 124 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part07.getD 12 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_07_124,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_07_125, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_125 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 125 j := by
  change ∀ j : Fin 24, 125 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 125)
      (generatedNinthLowerSpinSourceQReplayWord 5 125 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 126 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_07 (13 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 125 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part07.getD 13 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_07_125,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_07_126, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_126 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 126 j := by
  change ∀ j : Fin 24, 126 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 126)
      (generatedNinthLowerSpinSourceQReplayWord 5 126 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 127 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_07 (14 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 126 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part07.getD 14 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_07_126,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_07_127, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_127 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 5 127 j := by
  change ∀ j : Fin 24, 127 < (generatedNinthLowerSpinSourceWord 5).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 5 127)
      (generatedNinthLowerSpinSourceQReplayWord 5 127 j)
      (generatedNinthLowerSpinSourceQReplayWord 5 128 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_05_part_07 (15 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 5 127 =
    generatedNinthLowerSpinLiteralQReplayLetters05Part07.getD 15 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_05_part_07_127,
    generatedNinth_lower_spin_literal_q_replay_prefix_05_part_07_128, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

/-- Every actual primitive in this sixteen-step block retains all full central coordinates. -/
theorem generatedNinth_lower_spin_source_q_replay_packet_05_part_07 :
    ∀ n : Fin 16, ∀ j : Fin 24,
      112 + n.val < 314 →
        generatedNinthLowerSpinSourceQReplayStepCondition 5
          ⟨112 + n.val, by omega⟩ j := by
  intro n j hn
  fin_cases n
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_112 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_113 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_114 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_115 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_116 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_117 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_118 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_119 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_120 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_121 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_122 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_123 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_124 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_125 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_126 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_127 j)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
