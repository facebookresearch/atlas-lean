/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingTensorCircuitData

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingTensorSourceFast

/-! Every starting column retains the full original source cache and right monomial. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
-- Check all eight original source columns in a bounded full-coordinate block.
private theorem block_00 : ∀ r : Fin 8, ∀ u : Fin 256,
    generatedRootEightIncomingTensorStageInteger 0 r ⟨0 * 256 + u.val, by omega⟩ =
      16 * generatedRootEightIncomingTensorPreInteger
        (generatedRootEightIncomingTensorSourceCache r) ⟨0 * 256 + u.val, by omega⟩ := by
  unfold generatedRootEightIncomingTensorPreInteger
  simp_rw [← generatedRootEight_incoming_tensor_source_fast_actual]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all eight original source columns in a bounded full-coordinate block.
private theorem block_01 : ∀ r : Fin 8, ∀ u : Fin 256,
    generatedRootEightIncomingTensorStageInteger 0 r ⟨1 * 256 + u.val, by omega⟩ =
      16 * generatedRootEightIncomingTensorPreInteger
        (generatedRootEightIncomingTensorSourceCache r) ⟨1 * 256 + u.val, by omega⟩ := by
  unfold generatedRootEightIncomingTensorPreInteger
  simp_rw [← generatedRootEight_incoming_tensor_source_fast_actual]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all eight original source columns in a bounded full-coordinate block.
private theorem block_02 : ∀ r : Fin 8, ∀ u : Fin 256,
    generatedRootEightIncomingTensorStageInteger 0 r ⟨2 * 256 + u.val, by omega⟩ =
      16 * generatedRootEightIncomingTensorPreInteger
        (generatedRootEightIncomingTensorSourceCache r) ⟨2 * 256 + u.val, by omega⟩ := by
  unfold generatedRootEightIncomingTensorPreInteger
  simp_rw [← generatedRootEight_incoming_tensor_source_fast_actual]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all eight original source columns in a bounded full-coordinate block.
private theorem block_03 : ∀ r : Fin 8, ∀ u : Fin 256,
    generatedRootEightIncomingTensorStageInteger 0 r ⟨3 * 256 + u.val, by omega⟩ =
      16 * generatedRootEightIncomingTensorPreInteger
        (generatedRootEightIncomingTensorSourceCache r) ⟨3 * 256 + u.val, by omega⟩ := by
  unfold generatedRootEightIncomingTensorPreInteger
  simp_rw [← generatedRootEight_incoming_tensor_source_fast_actual]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all eight original source columns in a bounded full-coordinate block.
private theorem block_04 : ∀ r : Fin 8, ∀ u : Fin 256,
    generatedRootEightIncomingTensorStageInteger 0 r ⟨4 * 256 + u.val, by omega⟩ =
      16 * generatedRootEightIncomingTensorPreInteger
        (generatedRootEightIncomingTensorSourceCache r) ⟨4 * 256 + u.val, by omega⟩ := by
  unfold generatedRootEightIncomingTensorPreInteger
  simp_rw [← generatedRootEight_incoming_tensor_source_fast_actual]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all eight original source columns in a bounded full-coordinate block.
private theorem block_05 : ∀ r : Fin 8, ∀ u : Fin 256,
    generatedRootEightIncomingTensorStageInteger 0 r ⟨5 * 256 + u.val, by omega⟩ =
      16 * generatedRootEightIncomingTensorPreInteger
        (generatedRootEightIncomingTensorSourceCache r) ⟨5 * 256 + u.val, by omega⟩ := by
  unfold generatedRootEightIncomingTensorPreInteger
  simp_rw [← generatedRootEight_incoming_tensor_source_fast_actual]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all eight original source columns in a bounded full-coordinate block.
private theorem block_06 : ∀ r : Fin 8, ∀ u : Fin 256,
    generatedRootEightIncomingTensorStageInteger 0 r ⟨6 * 256 + u.val, by omega⟩ =
      16 * generatedRootEightIncomingTensorPreInteger
        (generatedRootEightIncomingTensorSourceCache r) ⟨6 * 256 + u.val, by omega⟩ := by
  unfold generatedRootEightIncomingTensorPreInteger
  simp_rw [← generatedRootEight_incoming_tensor_source_fast_actual]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all eight original source columns in a bounded full-coordinate block.
private theorem block_07 : ∀ r : Fin 8, ∀ u : Fin 256,
    generatedRootEightIncomingTensorStageInteger 0 r ⟨7 * 256 + u.val, by omega⟩ =
      16 * generatedRootEightIncomingTensorPreInteger
        (generatedRootEightIncomingTensorSourceCache r) ⟨7 * 256 + u.val, by omega⟩ := by
  unfold generatedRootEightIncomingTensorPreInteger
  simp_rw [← generatedRootEight_incoming_tensor_source_fast_actual]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all eight original source columns in a bounded full-coordinate block.
private theorem block_08 : ∀ r : Fin 8, ∀ u : Fin 256,
    generatedRootEightIncomingTensorStageInteger 0 r ⟨8 * 256 + u.val, by omega⟩ =
      16 * generatedRootEightIncomingTensorPreInteger
        (generatedRootEightIncomingTensorSourceCache r) ⟨8 * 256 + u.val, by omega⟩ := by
  unfold generatedRootEightIncomingTensorPreInteger
  simp_rw [← generatedRootEight_incoming_tensor_source_fast_actual]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all eight original source columns in a bounded full-coordinate block.
private theorem block_09 : ∀ r : Fin 8, ∀ u : Fin 256,
    generatedRootEightIncomingTensorStageInteger 0 r ⟨9 * 256 + u.val, by omega⟩ =
      16 * generatedRootEightIncomingTensorPreInteger
        (generatedRootEightIncomingTensorSourceCache r) ⟨9 * 256 + u.val, by omega⟩ := by
  unfold generatedRootEightIncomingTensorPreInteger
  simp_rw [← generatedRootEight_incoming_tensor_source_fast_actual]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all eight original source columns in a bounded full-coordinate block.
private theorem block_10 : ∀ r : Fin 8, ∀ u : Fin 256,
    generatedRootEightIncomingTensorStageInteger 0 r ⟨10 * 256 + u.val, by omega⟩ =
      16 * generatedRootEightIncomingTensorPreInteger
        (generatedRootEightIncomingTensorSourceCache r) ⟨10 * 256 + u.val, by omega⟩ := by
  unfold generatedRootEightIncomingTensorPreInteger
  simp_rw [← generatedRootEight_incoming_tensor_source_fast_actual]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all eight original source columns in a bounded full-coordinate block.
private theorem block_11 : ∀ r : Fin 8, ∀ u : Fin 256,
    generatedRootEightIncomingTensorStageInteger 0 r ⟨11 * 256 + u.val, by omega⟩ =
      16 * generatedRootEightIncomingTensorPreInteger
        (generatedRootEightIncomingTensorSourceCache r) ⟨11 * 256 + u.val, by omega⟩ := by
  unfold generatedRootEightIncomingTensorPreInteger
  simp_rw [← generatedRootEight_incoming_tensor_source_fast_actual]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all eight original source columns in a bounded full-coordinate block.
private theorem block_12 : ∀ r : Fin 8, ∀ u : Fin 256,
    generatedRootEightIncomingTensorStageInteger 0 r ⟨12 * 256 + u.val, by omega⟩ =
      16 * generatedRootEightIncomingTensorPreInteger
        (generatedRootEightIncomingTensorSourceCache r) ⟨12 * 256 + u.val, by omega⟩ := by
  unfold generatedRootEightIncomingTensorPreInteger
  simp_rw [← generatedRootEight_incoming_tensor_source_fast_actual]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all eight original source columns in a bounded full-coordinate block.
private theorem block_13 : ∀ r : Fin 8, ∀ u : Fin 256,
    generatedRootEightIncomingTensorStageInteger 0 r ⟨13 * 256 + u.val, by omega⟩ =
      16 * generatedRootEightIncomingTensorPreInteger
        (generatedRootEightIncomingTensorSourceCache r) ⟨13 * 256 + u.val, by omega⟩ := by
  unfold generatedRootEightIncomingTensorPreInteger
  simp_rw [← generatedRootEight_incoming_tensor_source_fast_actual]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all eight original source columns in a bounded full-coordinate block.
private theorem block_14 : ∀ r : Fin 8, ∀ u : Fin 256,
    generatedRootEightIncomingTensorStageInteger 0 r ⟨14 * 256 + u.val, by omega⟩ =
      16 * generatedRootEightIncomingTensorPreInteger
        (generatedRootEightIncomingTensorSourceCache r) ⟨14 * 256 + u.val, by omega⟩ := by
  unfold generatedRootEightIncomingTensorPreInteger
  simp_rw [← generatedRootEight_incoming_tensor_source_fast_actual]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all eight original source columns in a bounded full-coordinate block.
private theorem block_15 : ∀ r : Fin 8, ∀ u : Fin 256,
    generatedRootEightIncomingTensorStageInteger 0 r ⟨15 * 256 + u.val, by omega⟩ =
      16 * generatedRootEightIncomingTensorPreInteger
        (generatedRootEightIncomingTensorSourceCache r) ⟨15 * 256 + u.val, by omega⟩ := by
  unfold generatedRootEightIncomingTensorPreInteger
  simp_rw [← generatedRootEight_incoming_tensor_source_fast_actual]
  decide +kernel

/-- Every complete bounded block has its original full coordinate certificate. -/
theorem generatedRootEight_incoming_tensor_start_blocks : ∀ b : Fin 16, ∀ r : Fin 8, ∀ u : Fin 256,
    generatedRootEightIncomingTensorStageInteger 0 r ⟨b.val * 256 + u.val, by omega⟩ =
      16 * generatedRootEightIncomingTensorPreInteger
        (generatedRootEightIncomingTensorSourceCache r) ⟨b.val * 256 + u.val, by omega⟩ := by
  intro b r u
  fin_cases b
  · exact block_00 r u
  · exact block_01 r u
  · exact block_02 r u
  · exact block_03 r u
  · exact block_04 r u
  · exact block_05 r u
  · exact block_06 r u
  · exact block_07 r u
  · exact block_08 r u
  · exact block_09 r u
  · exact block_10 r u
  · exact block_11 r u
  · exact block_12 r u
  · exact block_13 r u
  · exact block_14 r u
  · exact block_15 r u

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
