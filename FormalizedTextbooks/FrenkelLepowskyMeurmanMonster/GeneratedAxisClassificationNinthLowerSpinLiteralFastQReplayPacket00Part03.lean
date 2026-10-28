/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinPrimitivePackedReplayGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinFastQMaskCentral
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinFastQPrefix03Certificates

/-! The exact original384 obligations after source-bound small full-prefix lookup replacement. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_048 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 0 48 j := by
  change ∀ j : Fin 24, 48 < (generatedNinthLowerSpinSourceWord 0).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 0 48)
      (generatedNinthLowerSpinSourceQReplayWord 0 48 j)
      (generatedNinthLowerSpinSourceQReplayWord 0 49 j)
  have hl := generatedNinth_lower_spin_fast_q_letter03 (0 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 0 48 =
    generatedNinthLowerSpinFastQLetter03 0 at hl
  rw [generatedNinth_lower_spin_fast_q_prefix03_048,
    generatedNinth_lower_spin_fast_q_prefix03_049, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_049 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 0 49 j := by
  change ∀ j : Fin 24, 49 < (generatedNinthLowerSpinSourceWord 0).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 0 49)
      (generatedNinthLowerSpinSourceQReplayWord 0 49 j)
      (generatedNinthLowerSpinSourceQReplayWord 0 50 j)
  have hl := generatedNinth_lower_spin_fast_q_letter03 (1 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 0 49 =
    generatedNinthLowerSpinFastQLetter03 1 at hl
  rw [generatedNinth_lower_spin_fast_q_prefix03_049,
    generatedNinth_lower_spin_fast_q_prefix03_050, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_050 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 0 50 j := by
  change ∀ j : Fin 24, 50 < (generatedNinthLowerSpinSourceWord 0).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 0 50)
      (generatedNinthLowerSpinSourceQReplayWord 0 50 j)
      (generatedNinthLowerSpinSourceQReplayWord 0 51 j)
  have hl := generatedNinth_lower_spin_fast_q_letter03 (2 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 0 50 =
    generatedNinthLowerSpinFastQLetter03 2 at hl
  rw [generatedNinth_lower_spin_fast_q_prefix03_050,
    generatedNinth_lower_spin_fast_q_prefix03_051, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_051 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 0 51 j := by
  change ∀ j : Fin 24, 51 < (generatedNinthLowerSpinSourceWord 0).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 0 51)
      (generatedNinthLowerSpinSourceQReplayWord 0 51 j)
      (generatedNinthLowerSpinSourceQReplayWord 0 52 j)
  have hl := generatedNinth_lower_spin_fast_q_letter03 (3 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 0 51 =
    generatedNinthLowerSpinFastQLetter03 3 at hl
  rw [generatedNinth_lower_spin_fast_q_prefix03_051,
    generatedNinth_lower_spin_fast_q_prefix03_052, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_052 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 0 52 j := by
  change ∀ j : Fin 24, 52 < (generatedNinthLowerSpinSourceWord 0).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 0 52)
      (generatedNinthLowerSpinSourceQReplayWord 0 52 j)
      (generatedNinthLowerSpinSourceQReplayWord 0 53 j)
  have hl := generatedNinth_lower_spin_fast_q_letter03 (4 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 0 52 =
    generatedNinthLowerSpinFastQLetter03 4 at hl
  rw [generatedNinth_lower_spin_fast_q_prefix03_052,
    generatedNinth_lower_spin_fast_q_prefix03_053, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_053 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 0 53 j := by
  change ∀ j : Fin 24, 53 < (generatedNinthLowerSpinSourceWord 0).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 0 53)
      (generatedNinthLowerSpinSourceQReplayWord 0 53 j)
      (generatedNinthLowerSpinSourceQReplayWord 0 54 j)
  have hl := generatedNinth_lower_spin_fast_q_letter03 (5 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 0 53 =
    generatedNinthLowerSpinFastQLetter03 5 at hl
  rw [generatedNinth_lower_spin_fast_q_prefix03_053,
    generatedNinth_lower_spin_fast_q_prefix03_054, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_054 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 0 54 j := by
  change ∀ j : Fin 24, 54 < (generatedNinthLowerSpinSourceWord 0).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 0 54)
      (generatedNinthLowerSpinSourceQReplayWord 0 54 j)
      (generatedNinthLowerSpinSourceQReplayWord 0 55 j)
  have hl := generatedNinth_lower_spin_fast_q_letter03 (6 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 0 54 =
    generatedNinthLowerSpinFastQLetter03 6 at hl
  rw [generatedNinth_lower_spin_fast_q_prefix03_054,
    generatedNinth_lower_spin_fast_q_prefix03_055, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_055 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 0 55 j := by
  change ∀ j : Fin 24, 55 < (generatedNinthLowerSpinSourceWord 0).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 0 55)
      (generatedNinthLowerSpinSourceQReplayWord 0 55 j)
      (generatedNinthLowerSpinSourceQReplayWord 0 56 j)
  have hl := generatedNinth_lower_spin_fast_q_letter03 (7 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 0 55 =
    generatedNinthLowerSpinFastQLetter03 7 at hl
  rw [generatedNinth_lower_spin_fast_q_prefix03_055,
    generatedNinth_lower_spin_fast_q_prefix03_056, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_056 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 0 56 j := by
  change ∀ j : Fin 24, 56 < (generatedNinthLowerSpinSourceWord 0).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 0 56)
      (generatedNinthLowerSpinSourceQReplayWord 0 56 j)
      (generatedNinthLowerSpinSourceQReplayWord 0 57 j)
  have hl := generatedNinth_lower_spin_fast_q_letter03 (8 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 0 56 =
    generatedNinthLowerSpinFastQLetter03 8 at hl
  rw [generatedNinth_lower_spin_fast_q_prefix03_056,
    generatedNinth_lower_spin_fast_q_prefix03_057, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_057 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 0 57 j := by
  change ∀ j : Fin 24, 57 < (generatedNinthLowerSpinSourceWord 0).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 0 57)
      (generatedNinthLowerSpinSourceQReplayWord 0 57 j)
      (generatedNinthLowerSpinSourceQReplayWord 0 58 j)
  have hl := generatedNinth_lower_spin_fast_q_letter03 (9 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 0 57 =
    generatedNinthLowerSpinFastQLetter03 9 at hl
  rw [generatedNinth_lower_spin_fast_q_prefix03_057,
    generatedNinth_lower_spin_fast_q_prefix03_058, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_058 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 0 58 j := by
  change ∀ j : Fin 24, 58 < (generatedNinthLowerSpinSourceWord 0).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 0 58)
      (generatedNinthLowerSpinSourceQReplayWord 0 58 j)
      (generatedNinthLowerSpinSourceQReplayWord 0 59 j)
  have hl := generatedNinth_lower_spin_fast_q_letter03 (10 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 0 58 =
    generatedNinthLowerSpinFastQLetter03 10 at hl
  rw [generatedNinth_lower_spin_fast_q_prefix03_058,
    generatedNinth_lower_spin_fast_q_prefix03_059, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_059 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 0 59 j := by
  change ∀ j : Fin 24, 59 < (generatedNinthLowerSpinSourceWord 0).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 0 59)
      (generatedNinthLowerSpinSourceQReplayWord 0 59 j)
      (generatedNinthLowerSpinSourceQReplayWord 0 60 j)
  have hl := generatedNinth_lower_spin_fast_q_letter03 (11 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 0 59 =
    generatedNinthLowerSpinFastQLetter03 11 at hl
  rw [generatedNinth_lower_spin_fast_q_prefix03_059,
    generatedNinth_lower_spin_fast_q_prefix03_060, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_060 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 0 60 j := by
  change ∀ j : Fin 24, 60 < (generatedNinthLowerSpinSourceWord 0).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 0 60)
      (generatedNinthLowerSpinSourceQReplayWord 0 60 j)
      (generatedNinthLowerSpinSourceQReplayWord 0 61 j)
  have hl := generatedNinth_lower_spin_fast_q_letter03 (12 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 0 60 =
    generatedNinthLowerSpinFastQLetter03 12 at hl
  rw [generatedNinth_lower_spin_fast_q_prefix03_060,
    generatedNinth_lower_spin_fast_q_prefix03_061, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_061 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 0 61 j := by
  change ∀ j : Fin 24, 61 < (generatedNinthLowerSpinSourceWord 0).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 0 61)
      (generatedNinthLowerSpinSourceQReplayWord 0 61 j)
      (generatedNinthLowerSpinSourceQReplayWord 0 62 j)
  have hl := generatedNinth_lower_spin_fast_q_letter03 (13 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 0 61 =
    generatedNinthLowerSpinFastQLetter03 13 at hl
  rw [generatedNinth_lower_spin_fast_q_prefix03_061,
    generatedNinth_lower_spin_fast_q_prefix03_062, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_062 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 0 62 j := by
  change ∀ j : Fin 24, 62 < (generatedNinthLowerSpinSourceWord 0).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 0 62)
      (generatedNinthLowerSpinSourceQReplayWord 0 62 j)
      (generatedNinthLowerSpinSourceQReplayWord 0 63 j)
  have hl := generatedNinth_lower_spin_fast_q_letter03 (14 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 0 62 =
    generatedNinthLowerSpinFastQLetter03 14 at hl
  rw [generatedNinth_lower_spin_fast_q_prefix03_062,
    generatedNinth_lower_spin_fast_q_prefix03_063, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Evaluate one actual primitive on all twenty-four literal full-Q prefix inputs.
private theorem step_063 : ∀ j : Fin 24,
    generatedNinthLowerSpinPrimitivePackedReplayStepCondition 0 63 j := by
  change ∀ j : Fin 24, 63 < (generatedNinthLowerSpinSourceWord 0).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter 0 63)
      (generatedNinthLowerSpinSourceQReplayWord 0 63 j)
      (generatedNinthLowerSpinSourceQReplayWord 0 64 j)
  have hl := generatedNinth_lower_spin_fast_q_letter03 (15 : Fin 16)
  change generatedNinthLowerSpinSourceQReplayLetter 0 63 =
    generatedNinthLowerSpinFastQLetter03 15 at hl
  rw [generatedNinth_lower_spin_fast_q_prefix03_063,
    generatedNinth_lower_spin_fast_q_prefix03_064, hl]
  unfold generatedNinthLowerSpinPrimitivePackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

/-- Every actual primitive in this sixteen-step block retains all full central coordinates. -/
theorem generatedNinth_lower_spin_literal_fast_q_replay_packet_00_part_03 :
    ∀ n : Fin 16, ∀ j : Fin 24,
      48 + n.val < 174 →
        generatedNinthLowerSpinSourceQReplayStepCondition 0
          ⟨48 + n.val, by omega⟩ j := by
  intro n j hn
  fin_cases n
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_048 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_049 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_050 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_051 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_052 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_053 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_054 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_055 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_056 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_057 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_058 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_059 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_060 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_061 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_062 j)
  · exact generatedNinth_lower_spin_primitive_packed_replay_step _ _ _ (step_063 j)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
