/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinPrimitivePackedReplayGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinLiteralQReplaySourcePacket04Part06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinFastQMaskCentral

/-! Sixteen bounded chronological primitive steps, all full Q coordinate images. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_096 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 96 j := by
  change ∀ j : Fin 24, 96 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 96)
      (generatedNinthLowerSpinSourceQReplayWord 4 96 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 97 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_06 (0 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 96 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part06.getD 0 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_06_096,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_06_097, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_097 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 97 j := by
  change ∀ j : Fin 24, 97 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 97)
      (generatedNinthLowerSpinSourceQReplayWord 4 97 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 98 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_06 (1 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 97 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part06.getD 1 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_06_097,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_06_098, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_098 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 98 j := by
  change ∀ j : Fin 24, 98 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 98)
      (generatedNinthLowerSpinSourceQReplayWord 4 98 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 99 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_06 (2 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 98 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part06.getD 2 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_06_098,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_06_099, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_099 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 99 j := by
  change ∀ j : Fin 24, 99 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 99)
      (generatedNinthLowerSpinSourceQReplayWord 4 99 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 100 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_06 (3 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 99 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part06.getD 3 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_06_099,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_06_100, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_100 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 100 j := by
  change ∀ j : Fin 24, 100 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 100)
      (generatedNinthLowerSpinSourceQReplayWord 4 100 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 101 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_06 (4 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 100 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part06.getD 4 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_06_100,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_06_101, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_101 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 101 j := by
  change ∀ j : Fin 24, 101 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 101)
      (generatedNinthLowerSpinSourceQReplayWord 4 101 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 102 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_06 (5 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 101 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part06.getD 5 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_06_101,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_06_102, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_102 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 102 j := by
  change ∀ j : Fin 24, 102 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 102)
      (generatedNinthLowerSpinSourceQReplayWord 4 102 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 103 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_06 (6 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 102 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part06.getD 6 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_06_102,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_06_103, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_103 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 103 j := by
  change ∀ j : Fin 24, 103 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 103)
      (generatedNinthLowerSpinSourceQReplayWord 4 103 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 104 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_06 (7 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 103 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part06.getD 7 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_06_103,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_06_104, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_104 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 104 j := by
  change ∀ j : Fin 24, 104 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 104)
      (generatedNinthLowerSpinSourceQReplayWord 4 104 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 105 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_06 (8 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 104 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part06.getD 8 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_06_104,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_06_105, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_105 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 105 j := by
  change ∀ j : Fin 24, 105 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 105)
      (generatedNinthLowerSpinSourceQReplayWord 4 105 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 106 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_06 (9 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 105 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part06.getD 9 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_06_105,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_06_106, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_106 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 106 j := by
  change ∀ j : Fin 24, 106 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 106)
      (generatedNinthLowerSpinSourceQReplayWord 4 106 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 107 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_06 (10 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 106 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part06.getD 10 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_06_106,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_06_107, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_107 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 107 j := by
  change ∀ j : Fin 24, 107 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 107)
      (generatedNinthLowerSpinSourceQReplayWord 4 107 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 108 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_06 (11 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 107 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part06.getD 11 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_06_107,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_06_108, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_108 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 108 j := by
  change ∀ j : Fin 24, 108 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 108)
      (generatedNinthLowerSpinSourceQReplayWord 4 108 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 109 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_06 (12 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 108 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part06.getD 12 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_06_108,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_06_109, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_109 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 109 j := by
  change ∀ j : Fin 24, 109 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 109)
      (generatedNinthLowerSpinSourceQReplayWord 4 109 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 110 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_06 (13 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 109 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part06.getD 13 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_06_109,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_06_110, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_110 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 110 j := by
  change ∀ j : Fin 24, 110 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 110)
      (generatedNinthLowerSpinSourceQReplayWord 4 110 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 111 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_06 (14 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 110 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part06.getD 14 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_06_110,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_06_111, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_111 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 4 111 j := by
  change ∀ j : Fin 24, 111 < (generatedNinthLowerSpinSourceWord 4).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 4 111)
      (generatedNinthLowerSpinSourceQReplayWord 4 111 j)
      (generatedNinthLowerSpinSourceQReplayWord 4 112 j)
  have hl := congrFun generatedNinth_lower_spin_literal_q_replay_letters_04_part_06 (15 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 4 111 =
    generatedNinthLowerSpinLiteralQReplayLetters04Part06.getD 15 (11, false) at hl
  rw [generatedNinth_lower_spin_literal_q_replay_prefix_04_part_06_111,
    generatedNinth_lower_spin_literal_q_replay_prefix_04_part_06_112, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

/-- Every actual primitive in this sixteen-step block retains all full central coordinates. -/
theorem generatedNinth_lower_spin_source_q_replay_packet_04_part_06 :
    ∀ n : Fin 16, ∀ j : Fin 24,
      96 + n.val < 175 →
        generatedNinthLowerSpinSourceQReplayStepCondition 4
          ⟨96 + n.val, by omega⟩ j := by
  intro n j hn
  fin_cases n
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_096 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_097 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_098 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_099 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_100 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_101 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_102 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_103 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_104 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_105 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_106 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_107 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_108 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_109 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_110 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_111 j)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
