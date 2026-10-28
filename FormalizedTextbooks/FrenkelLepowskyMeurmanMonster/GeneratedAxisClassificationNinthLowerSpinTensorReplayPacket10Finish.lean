/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinTensorBoundaryRows

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinTensorCircuitData

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinTensorBoundedQuantifier

/-! Full 4096-coordinate column packets for generator 10 finish. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
-- Check one complete normalized integer circuit stage on a single source column.
private theorem column_00 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorPostInteger 10
      (fun m => generatedNinthLowerSpinTensorStageInteger 10 5 m 0) n =
        (generatedNinthLowerSpinTensorSpatialDenominator 10 : ℤ) *
          generatedNinthLowerSpinTensorInputInteger n 0 := by
  apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
  change ∀ b : Fin 16, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorPostInteger 10
      (fun m => generatedNinthLowerSpinTensorStageInteger 10 5 m 0)
        (generatedNinthLowerSpinTensorBlockIndex b u) =
      (generatedNinthLowerSpinTensorSpatialDenominator 10 : ℤ) *
        generatedNinthLowerSpinTensorInputInteger (generatedNinthLowerSpinTensorBlockIndex b u) 0
  dsimp only [generatedNinthLowerSpinTensorPostInteger,
    generatedNinthLowerSpinTensorStageInteger, generatedNinthLowerSpinTensorInputInteger]
  simp_rw [generatedNinth_lower_spin_tensor_post_label_block,
    generatedNinth_lower_spin_tensor_post_sign_block,
    generatedNinth_lower_spin_tensor_packed_coordinate_block]
  intro b
  fin_cases b <;>
    norm_num only [generatedNinthLowerSpinTensorStageWords,
      generatedNinthLowerSpinTensorStageWords10,
      generatedNinthLowerSpinTensorPostLabelWords, generatedNinthLowerSpinTensorPostSignWords,
      generatedNinthLowerSpinTensorSpatialDenominator, generatedNinthLowerSpinTensorInputWords]
  all_goals decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete normalized integer circuit stage on a single source column.
private theorem column_01 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorPostInteger 10
      (fun m => generatedNinthLowerSpinTensorStageInteger 10 5 m 1) n =
        (generatedNinthLowerSpinTensorSpatialDenominator 10 : ℤ) *
          generatedNinthLowerSpinTensorInputInteger n 1 := by
  apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
  change ∀ b : Fin 16, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorPostInteger 10
      (fun m => generatedNinthLowerSpinTensorStageInteger 10 5 m 1)
        (generatedNinthLowerSpinTensorBlockIndex b u) =
      (generatedNinthLowerSpinTensorSpatialDenominator 10 : ℤ) *
        generatedNinthLowerSpinTensorInputInteger (generatedNinthLowerSpinTensorBlockIndex b u) 1
  dsimp only [generatedNinthLowerSpinTensorPostInteger,
    generatedNinthLowerSpinTensorStageInteger, generatedNinthLowerSpinTensorInputInteger]
  simp_rw [generatedNinth_lower_spin_tensor_post_label_block,
    generatedNinth_lower_spin_tensor_post_sign_block,
    generatedNinth_lower_spin_tensor_packed_coordinate_block]
  intro b
  fin_cases b <;>
    norm_num only [generatedNinthLowerSpinTensorStageWords,
      generatedNinthLowerSpinTensorStageWords10,
      generatedNinthLowerSpinTensorPostLabelWords, generatedNinthLowerSpinTensorPostSignWords,
      generatedNinthLowerSpinTensorSpatialDenominator, generatedNinthLowerSpinTensorInputWords]
  all_goals decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete normalized integer circuit stage on a single source column.
private theorem column_02 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorPostInteger 10
      (fun m => generatedNinthLowerSpinTensorStageInteger 10 5 m 2) n =
        (generatedNinthLowerSpinTensorSpatialDenominator 10 : ℤ) *
          generatedNinthLowerSpinTensorInputInteger n 2 := by
  apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
  change ∀ b : Fin 16, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorPostInteger 10
      (fun m => generatedNinthLowerSpinTensorStageInteger 10 5 m 2)
        (generatedNinthLowerSpinTensorBlockIndex b u) =
      (generatedNinthLowerSpinTensorSpatialDenominator 10 : ℤ) *
        generatedNinthLowerSpinTensorInputInteger (generatedNinthLowerSpinTensorBlockIndex b u) 2
  dsimp only [generatedNinthLowerSpinTensorPostInteger,
    generatedNinthLowerSpinTensorStageInteger, generatedNinthLowerSpinTensorInputInteger]
  simp_rw [generatedNinth_lower_spin_tensor_post_label_block,
    generatedNinth_lower_spin_tensor_post_sign_block,
    generatedNinth_lower_spin_tensor_packed_coordinate_block]
  intro b
  fin_cases b <;>
    norm_num only [generatedNinthLowerSpinTensorStageWords,
      generatedNinthLowerSpinTensorStageWords10,
      generatedNinthLowerSpinTensorPostLabelWords, generatedNinthLowerSpinTensorPostSignWords,
      generatedNinthLowerSpinTensorSpatialDenominator, generatedNinthLowerSpinTensorInputWords]
  all_goals decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete normalized integer circuit stage on a single source column.
private theorem column_03 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorPostInteger 10
      (fun m => generatedNinthLowerSpinTensorStageInteger 10 5 m 3) n =
        (generatedNinthLowerSpinTensorSpatialDenominator 10 : ℤ) *
          generatedNinthLowerSpinTensorInputInteger n 3 := by
  apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
  change ∀ b : Fin 16, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorPostInteger 10
      (fun m => generatedNinthLowerSpinTensorStageInteger 10 5 m 3)
        (generatedNinthLowerSpinTensorBlockIndex b u) =
      (generatedNinthLowerSpinTensorSpatialDenominator 10 : ℤ) *
        generatedNinthLowerSpinTensorInputInteger (generatedNinthLowerSpinTensorBlockIndex b u) 3
  dsimp only [generatedNinthLowerSpinTensorPostInteger,
    generatedNinthLowerSpinTensorStageInteger, generatedNinthLowerSpinTensorInputInteger]
  simp_rw [generatedNinth_lower_spin_tensor_post_label_block,
    generatedNinth_lower_spin_tensor_post_sign_block,
    generatedNinth_lower_spin_tensor_packed_coordinate_block]
  intro b
  fin_cases b <;>
    norm_num only [generatedNinthLowerSpinTensorStageWords,
      generatedNinthLowerSpinTensorStageWords10,
      generatedNinthLowerSpinTensorPostLabelWords, generatedNinthLowerSpinTensorPostSignWords,
      generatedNinthLowerSpinTensorSpatialDenominator, generatedNinthLowerSpinTensorInputWords]
  all_goals decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete normalized integer circuit stage on a single source column.
private theorem column_04 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorPostInteger 10
      (fun m => generatedNinthLowerSpinTensorStageInteger 10 5 m 4) n =
        (generatedNinthLowerSpinTensorSpatialDenominator 10 : ℤ) *
          generatedNinthLowerSpinTensorInputInteger n 4 := by
  apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
  change ∀ b : Fin 16, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorPostInteger 10
      (fun m => generatedNinthLowerSpinTensorStageInteger 10 5 m 4)
        (generatedNinthLowerSpinTensorBlockIndex b u) =
      (generatedNinthLowerSpinTensorSpatialDenominator 10 : ℤ) *
        generatedNinthLowerSpinTensorInputInteger (generatedNinthLowerSpinTensorBlockIndex b u) 4
  dsimp only [generatedNinthLowerSpinTensorPostInteger,
    generatedNinthLowerSpinTensorStageInteger, generatedNinthLowerSpinTensorInputInteger]
  simp_rw [generatedNinth_lower_spin_tensor_post_label_block,
    generatedNinth_lower_spin_tensor_post_sign_block,
    generatedNinth_lower_spin_tensor_packed_coordinate_block]
  intro b
  fin_cases b <;>
    norm_num only [generatedNinthLowerSpinTensorStageWords,
      generatedNinthLowerSpinTensorStageWords10,
      generatedNinthLowerSpinTensorPostLabelWords, generatedNinthLowerSpinTensorPostSignWords,
      generatedNinthLowerSpinTensorSpatialDenominator, generatedNinthLowerSpinTensorInputWords]
  all_goals decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete normalized integer circuit stage on a single source column.
private theorem column_05 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorPostInteger 10
      (fun m => generatedNinthLowerSpinTensorStageInteger 10 5 m 5) n =
        (generatedNinthLowerSpinTensorSpatialDenominator 10 : ℤ) *
          generatedNinthLowerSpinTensorInputInteger n 5 := by
  apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
  change ∀ b : Fin 16, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorPostInteger 10
      (fun m => generatedNinthLowerSpinTensorStageInteger 10 5 m 5)
        (generatedNinthLowerSpinTensorBlockIndex b u) =
      (generatedNinthLowerSpinTensorSpatialDenominator 10 : ℤ) *
        generatedNinthLowerSpinTensorInputInteger (generatedNinthLowerSpinTensorBlockIndex b u) 5
  dsimp only [generatedNinthLowerSpinTensorPostInteger,
    generatedNinthLowerSpinTensorStageInteger, generatedNinthLowerSpinTensorInputInteger]
  simp_rw [generatedNinth_lower_spin_tensor_post_label_block,
    generatedNinth_lower_spin_tensor_post_sign_block,
    generatedNinth_lower_spin_tensor_packed_coordinate_block]
  intro b
  fin_cases b <;>
    norm_num only [generatedNinthLowerSpinTensorStageWords,
      generatedNinthLowerSpinTensorStageWords10,
      generatedNinthLowerSpinTensorPostLabelWords, generatedNinthLowerSpinTensorPostSignWords,
      generatedNinthLowerSpinTensorSpatialDenominator, generatedNinthLowerSpinTensorInputWords]
  all_goals decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete normalized integer circuit stage on a single source column.
private theorem column_06 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorPostInteger 10
      (fun m => generatedNinthLowerSpinTensorStageInteger 10 5 m 6) n =
        (generatedNinthLowerSpinTensorSpatialDenominator 10 : ℤ) *
          generatedNinthLowerSpinTensorInputInteger n 6 := by
  apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
  change ∀ b : Fin 16, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorPostInteger 10
      (fun m => generatedNinthLowerSpinTensorStageInteger 10 5 m 6)
        (generatedNinthLowerSpinTensorBlockIndex b u) =
      (generatedNinthLowerSpinTensorSpatialDenominator 10 : ℤ) *
        generatedNinthLowerSpinTensorInputInteger (generatedNinthLowerSpinTensorBlockIndex b u) 6
  dsimp only [generatedNinthLowerSpinTensorPostInteger,
    generatedNinthLowerSpinTensorStageInteger, generatedNinthLowerSpinTensorInputInteger]
  simp_rw [generatedNinth_lower_spin_tensor_post_label_block,
    generatedNinth_lower_spin_tensor_post_sign_block,
    generatedNinth_lower_spin_tensor_packed_coordinate_block]
  intro b
  fin_cases b <;>
    norm_num only [generatedNinthLowerSpinTensorStageWords,
      generatedNinthLowerSpinTensorStageWords10,
      generatedNinthLowerSpinTensorPostLabelWords, generatedNinthLowerSpinTensorPostSignWords,
      generatedNinthLowerSpinTensorSpatialDenominator, generatedNinthLowerSpinTensorInputWords]
  all_goals decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete normalized integer circuit stage on a single source column.
private theorem column_07 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorPostInteger 10
      (fun m => generatedNinthLowerSpinTensorStageInteger 10 5 m 7) n =
        (generatedNinthLowerSpinTensorSpatialDenominator 10 : ℤ) *
          generatedNinthLowerSpinTensorInputInteger n 7 := by
  apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
  change ∀ b : Fin 16, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorPostInteger 10
      (fun m => generatedNinthLowerSpinTensorStageInteger 10 5 m 7)
        (generatedNinthLowerSpinTensorBlockIndex b u) =
      (generatedNinthLowerSpinTensorSpatialDenominator 10 : ℤ) *
        generatedNinthLowerSpinTensorInputInteger (generatedNinthLowerSpinTensorBlockIndex b u) 7
  dsimp only [generatedNinthLowerSpinTensorPostInteger,
    generatedNinthLowerSpinTensorStageInteger, generatedNinthLowerSpinTensorInputInteger]
  simp_rw [generatedNinth_lower_spin_tensor_post_label_block,
    generatedNinth_lower_spin_tensor_post_sign_block,
    generatedNinth_lower_spin_tensor_packed_coordinate_block]
  intro b
  fin_cases b <;>
    norm_num only [generatedNinthLowerSpinTensorStageWords,
      generatedNinthLowerSpinTensorStageWords10,
      generatedNinthLowerSpinTensorPostLabelWords, generatedNinthLowerSpinTensorPostSignWords,
      generatedNinthLowerSpinTensorSpatialDenominator, generatedNinthLowerSpinTensorInputWords]
  all_goals decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete normalized integer circuit stage on a single source column.
private theorem column_08 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorPostInteger 10
      (fun m => generatedNinthLowerSpinTensorStageInteger 10 5 m 8) n =
        (generatedNinthLowerSpinTensorSpatialDenominator 10 : ℤ) *
          generatedNinthLowerSpinTensorInputInteger n 8 := by
  apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
  change ∀ b : Fin 16, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorPostInteger 10
      (fun m => generatedNinthLowerSpinTensorStageInteger 10 5 m 8)
        (generatedNinthLowerSpinTensorBlockIndex b u) =
      (generatedNinthLowerSpinTensorSpatialDenominator 10 : ℤ) *
        generatedNinthLowerSpinTensorInputInteger (generatedNinthLowerSpinTensorBlockIndex b u) 8
  dsimp only [generatedNinthLowerSpinTensorPostInteger,
    generatedNinthLowerSpinTensorStageInteger, generatedNinthLowerSpinTensorInputInteger]
  simp_rw [generatedNinth_lower_spin_tensor_post_label_block,
    generatedNinth_lower_spin_tensor_post_sign_block,
    generatedNinth_lower_spin_tensor_packed_coordinate_block]
  intro b
  fin_cases b <;>
    norm_num only [generatedNinthLowerSpinTensorStageWords,
      generatedNinthLowerSpinTensorStageWords10,
      generatedNinthLowerSpinTensorPostLabelWords, generatedNinthLowerSpinTensorPostSignWords,
      generatedNinthLowerSpinTensorSpatialDenominator, generatedNinthLowerSpinTensorInputWords]
  all_goals decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete normalized integer circuit stage on a single source column.
private theorem column_09 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorPostInteger 10
      (fun m => generatedNinthLowerSpinTensorStageInteger 10 5 m 9) n =
        (generatedNinthLowerSpinTensorSpatialDenominator 10 : ℤ) *
          generatedNinthLowerSpinTensorInputInteger n 9 := by
  apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
  change ∀ b : Fin 16, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorPostInteger 10
      (fun m => generatedNinthLowerSpinTensorStageInteger 10 5 m 9)
        (generatedNinthLowerSpinTensorBlockIndex b u) =
      (generatedNinthLowerSpinTensorSpatialDenominator 10 : ℤ) *
        generatedNinthLowerSpinTensorInputInteger (generatedNinthLowerSpinTensorBlockIndex b u) 9
  dsimp only [generatedNinthLowerSpinTensorPostInteger,
    generatedNinthLowerSpinTensorStageInteger, generatedNinthLowerSpinTensorInputInteger]
  simp_rw [generatedNinth_lower_spin_tensor_post_label_block,
    generatedNinth_lower_spin_tensor_post_sign_block,
    generatedNinth_lower_spin_tensor_packed_coordinate_block]
  intro b
  fin_cases b <;>
    norm_num only [generatedNinthLowerSpinTensorStageWords,
      generatedNinthLowerSpinTensorStageWords10,
      generatedNinthLowerSpinTensorPostLabelWords, generatedNinthLowerSpinTensorPostSignWords,
      generatedNinthLowerSpinTensorSpatialDenominator, generatedNinthLowerSpinTensorInputWords]
  all_goals decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete normalized integer circuit stage on a single source column.
private theorem column_10 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorPostInteger 10
      (fun m => generatedNinthLowerSpinTensorStageInteger 10 5 m 10) n =
        (generatedNinthLowerSpinTensorSpatialDenominator 10 : ℤ) *
          generatedNinthLowerSpinTensorInputInteger n 10 := by
  apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
  change ∀ b : Fin 16, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorPostInteger 10
      (fun m => generatedNinthLowerSpinTensorStageInteger 10 5 m 10)
        (generatedNinthLowerSpinTensorBlockIndex b u) =
      (generatedNinthLowerSpinTensorSpatialDenominator 10 : ℤ) *
        generatedNinthLowerSpinTensorInputInteger (generatedNinthLowerSpinTensorBlockIndex b u) 10
  dsimp only [generatedNinthLowerSpinTensorPostInteger,
    generatedNinthLowerSpinTensorStageInteger, generatedNinthLowerSpinTensorInputInteger]
  simp_rw [generatedNinth_lower_spin_tensor_post_label_block,
    generatedNinth_lower_spin_tensor_post_sign_block,
    generatedNinth_lower_spin_tensor_packed_coordinate_block]
  intro b
  fin_cases b <;>
    norm_num only [generatedNinthLowerSpinTensorStageWords,
      generatedNinthLowerSpinTensorStageWords10,
      generatedNinthLowerSpinTensorPostLabelWords, generatedNinthLowerSpinTensorPostSignWords,
      generatedNinthLowerSpinTensorSpatialDenominator, generatedNinthLowerSpinTensorInputWords]
  all_goals decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete normalized integer circuit stage on a single source column.
private theorem column_11 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorPostInteger 10
      (fun m => generatedNinthLowerSpinTensorStageInteger 10 5 m 11) n =
        (generatedNinthLowerSpinTensorSpatialDenominator 10 : ℤ) *
          generatedNinthLowerSpinTensorInputInteger n 11 := by
  apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
  change ∀ b : Fin 16, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorPostInteger 10
      (fun m => generatedNinthLowerSpinTensorStageInteger 10 5 m 11)
        (generatedNinthLowerSpinTensorBlockIndex b u) =
      (generatedNinthLowerSpinTensorSpatialDenominator 10 : ℤ) *
        generatedNinthLowerSpinTensorInputInteger (generatedNinthLowerSpinTensorBlockIndex b u) 11
  dsimp only [generatedNinthLowerSpinTensorPostInteger,
    generatedNinthLowerSpinTensorStageInteger, generatedNinthLowerSpinTensorInputInteger]
  simp_rw [generatedNinth_lower_spin_tensor_post_label_block,
    generatedNinth_lower_spin_tensor_post_sign_block,
    generatedNinth_lower_spin_tensor_packed_coordinate_block]
  intro b
  fin_cases b <;>
    norm_num only [generatedNinthLowerSpinTensorStageWords,
      generatedNinthLowerSpinTensorStageWords10,
      generatedNinthLowerSpinTensorPostLabelWords, generatedNinthLowerSpinTensorPostSignWords,
      generatedNinthLowerSpinTensorSpatialDenominator, generatedNinthLowerSpinTensorInputWords]
  all_goals decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete normalized integer circuit stage on a single source column.
private theorem column_12 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorPostInteger 10
      (fun m => generatedNinthLowerSpinTensorStageInteger 10 5 m 12) n =
        (generatedNinthLowerSpinTensorSpatialDenominator 10 : ℤ) *
          generatedNinthLowerSpinTensorInputInteger n 12 := by
  apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
  change ∀ b : Fin 16, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorPostInteger 10
      (fun m => generatedNinthLowerSpinTensorStageInteger 10 5 m 12)
        (generatedNinthLowerSpinTensorBlockIndex b u) =
      (generatedNinthLowerSpinTensorSpatialDenominator 10 : ℤ) *
        generatedNinthLowerSpinTensorInputInteger (generatedNinthLowerSpinTensorBlockIndex b u) 12
  dsimp only [generatedNinthLowerSpinTensorPostInteger,
    generatedNinthLowerSpinTensorStageInteger, generatedNinthLowerSpinTensorInputInteger]
  simp_rw [generatedNinth_lower_spin_tensor_post_label_block,
    generatedNinth_lower_spin_tensor_post_sign_block,
    generatedNinth_lower_spin_tensor_packed_coordinate_block]
  intro b
  fin_cases b <;>
    norm_num only [generatedNinthLowerSpinTensorStageWords,
      generatedNinthLowerSpinTensorStageWords10,
      generatedNinthLowerSpinTensorPostLabelWords, generatedNinthLowerSpinTensorPostSignWords,
      generatedNinthLowerSpinTensorSpatialDenominator, generatedNinthLowerSpinTensorInputWords]
  all_goals decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete normalized integer circuit stage on a single source column.
private theorem column_13 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorPostInteger 10
      (fun m => generatedNinthLowerSpinTensorStageInteger 10 5 m 13) n =
        (generatedNinthLowerSpinTensorSpatialDenominator 10 : ℤ) *
          generatedNinthLowerSpinTensorInputInteger n 13 := by
  apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
  change ∀ b : Fin 16, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorPostInteger 10
      (fun m => generatedNinthLowerSpinTensorStageInteger 10 5 m 13)
        (generatedNinthLowerSpinTensorBlockIndex b u) =
      (generatedNinthLowerSpinTensorSpatialDenominator 10 : ℤ) *
        generatedNinthLowerSpinTensorInputInteger (generatedNinthLowerSpinTensorBlockIndex b u) 13
  dsimp only [generatedNinthLowerSpinTensorPostInteger,
    generatedNinthLowerSpinTensorStageInteger, generatedNinthLowerSpinTensorInputInteger]
  simp_rw [generatedNinth_lower_spin_tensor_post_label_block,
    generatedNinth_lower_spin_tensor_post_sign_block,
    generatedNinth_lower_spin_tensor_packed_coordinate_block]
  intro b
  fin_cases b <;>
    norm_num only [generatedNinthLowerSpinTensorStageWords,
      generatedNinthLowerSpinTensorStageWords10,
      generatedNinthLowerSpinTensorPostLabelWords, generatedNinthLowerSpinTensorPostSignWords,
      generatedNinthLowerSpinTensorSpatialDenominator, generatedNinthLowerSpinTensorInputWords]
  all_goals decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete normalized integer circuit stage on a single source column.
private theorem column_14 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorPostInteger 10
      (fun m => generatedNinthLowerSpinTensorStageInteger 10 5 m 14) n =
        (generatedNinthLowerSpinTensorSpatialDenominator 10 : ℤ) *
          generatedNinthLowerSpinTensorInputInteger n 14 := by
  apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
  change ∀ b : Fin 16, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorPostInteger 10
      (fun m => generatedNinthLowerSpinTensorStageInteger 10 5 m 14)
        (generatedNinthLowerSpinTensorBlockIndex b u) =
      (generatedNinthLowerSpinTensorSpatialDenominator 10 : ℤ) *
        generatedNinthLowerSpinTensorInputInteger (generatedNinthLowerSpinTensorBlockIndex b u) 14
  dsimp only [generatedNinthLowerSpinTensorPostInteger,
    generatedNinthLowerSpinTensorStageInteger, generatedNinthLowerSpinTensorInputInteger]
  simp_rw [generatedNinth_lower_spin_tensor_post_label_block,
    generatedNinth_lower_spin_tensor_post_sign_block,
    generatedNinth_lower_spin_tensor_packed_coordinate_block]
  intro b
  fin_cases b <;>
    norm_num only [generatedNinthLowerSpinTensorStageWords,
      generatedNinthLowerSpinTensorStageWords10,
      generatedNinthLowerSpinTensorPostLabelWords, generatedNinthLowerSpinTensorPostSignWords,
      generatedNinthLowerSpinTensorSpatialDenominator, generatedNinthLowerSpinTensorInputWords]
  all_goals decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete normalized integer circuit stage on a single source column.
private theorem column_15 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorPostInteger 10
      (fun m => generatedNinthLowerSpinTensorStageInteger 10 5 m 15) n =
        (generatedNinthLowerSpinTensorSpatialDenominator 10 : ℤ) *
          generatedNinthLowerSpinTensorInputInteger n 15 := by
  apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
  change ∀ b : Fin 16, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorPostInteger 10
      (fun m => generatedNinthLowerSpinTensorStageInteger 10 5 m 15)
        (generatedNinthLowerSpinTensorBlockIndex b u) =
      (generatedNinthLowerSpinTensorSpatialDenominator 10 : ℤ) *
        generatedNinthLowerSpinTensorInputInteger (generatedNinthLowerSpinTensorBlockIndex b u) 15
  dsimp only [generatedNinthLowerSpinTensorPostInteger,
    generatedNinthLowerSpinTensorStageInteger, generatedNinthLowerSpinTensorInputInteger]
  simp_rw [generatedNinth_lower_spin_tensor_post_label_block,
    generatedNinth_lower_spin_tensor_post_sign_block,
    generatedNinth_lower_spin_tensor_packed_coordinate_block]
  intro b
  fin_cases b <;>
    norm_num only [generatedNinthLowerSpinTensorStageWords,
      generatedNinthLowerSpinTensorStageWords10,
      generatedNinthLowerSpinTensorPostLabelWords, generatedNinthLowerSpinTensorPostSignWords,
      generatedNinthLowerSpinTensorSpatialDenominator, generatedNinthLowerSpinTensorInputWords]
  all_goals decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete normalized integer circuit stage on a single source column.
private theorem column_16 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorPostInteger 10
      (fun m => generatedNinthLowerSpinTensorStageInteger 10 5 m 16) n =
        (generatedNinthLowerSpinTensorSpatialDenominator 10 : ℤ) *
          generatedNinthLowerSpinTensorInputInteger n 16 := by
  apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
  change ∀ b : Fin 16, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorPostInteger 10
      (fun m => generatedNinthLowerSpinTensorStageInteger 10 5 m 16)
        (generatedNinthLowerSpinTensorBlockIndex b u) =
      (generatedNinthLowerSpinTensorSpatialDenominator 10 : ℤ) *
        generatedNinthLowerSpinTensorInputInteger (generatedNinthLowerSpinTensorBlockIndex b u) 16
  dsimp only [generatedNinthLowerSpinTensorPostInteger,
    generatedNinthLowerSpinTensorStageInteger, generatedNinthLowerSpinTensorInputInteger]
  simp_rw [generatedNinth_lower_spin_tensor_post_label_block,
    generatedNinth_lower_spin_tensor_post_sign_block,
    generatedNinth_lower_spin_tensor_packed_coordinate_block]
  intro b
  fin_cases b <;>
    norm_num only [generatedNinthLowerSpinTensorStageWords,
      generatedNinthLowerSpinTensorStageWords10,
      generatedNinthLowerSpinTensorPostLabelWords, generatedNinthLowerSpinTensorPostSignWords,
      generatedNinthLowerSpinTensorSpatialDenominator, generatedNinthLowerSpinTensorInputWords]
  all_goals decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete normalized integer circuit stage on a single source column.
private theorem column_17 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorPostInteger 10
      (fun m => generatedNinthLowerSpinTensorStageInteger 10 5 m 17) n =
        (generatedNinthLowerSpinTensorSpatialDenominator 10 : ℤ) *
          generatedNinthLowerSpinTensorInputInteger n 17 := by
  apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
  change ∀ b : Fin 16, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorPostInteger 10
      (fun m => generatedNinthLowerSpinTensorStageInteger 10 5 m 17)
        (generatedNinthLowerSpinTensorBlockIndex b u) =
      (generatedNinthLowerSpinTensorSpatialDenominator 10 : ℤ) *
        generatedNinthLowerSpinTensorInputInteger (generatedNinthLowerSpinTensorBlockIndex b u) 17
  dsimp only [generatedNinthLowerSpinTensorPostInteger,
    generatedNinthLowerSpinTensorStageInteger, generatedNinthLowerSpinTensorInputInteger]
  simp_rw [generatedNinth_lower_spin_tensor_post_label_block,
    generatedNinth_lower_spin_tensor_post_sign_block,
    generatedNinth_lower_spin_tensor_packed_coordinate_block]
  intro b
  fin_cases b <;>
    norm_num only [generatedNinthLowerSpinTensorStageWords,
      generatedNinthLowerSpinTensorStageWords10,
      generatedNinthLowerSpinTensorPostLabelWords, generatedNinthLowerSpinTensorPostSignWords,
      generatedNinthLowerSpinTensorSpatialDenominator, generatedNinthLowerSpinTensorInputWords]
  all_goals decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete normalized integer circuit stage on a single source column.
private theorem column_18 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorPostInteger 10
      (fun m => generatedNinthLowerSpinTensorStageInteger 10 5 m 18) n =
        (generatedNinthLowerSpinTensorSpatialDenominator 10 : ℤ) *
          generatedNinthLowerSpinTensorInputInteger n 18 := by
  apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
  change ∀ b : Fin 16, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorPostInteger 10
      (fun m => generatedNinthLowerSpinTensorStageInteger 10 5 m 18)
        (generatedNinthLowerSpinTensorBlockIndex b u) =
      (generatedNinthLowerSpinTensorSpatialDenominator 10 : ℤ) *
        generatedNinthLowerSpinTensorInputInteger (generatedNinthLowerSpinTensorBlockIndex b u) 18
  dsimp only [generatedNinthLowerSpinTensorPostInteger,
    generatedNinthLowerSpinTensorStageInteger, generatedNinthLowerSpinTensorInputInteger]
  simp_rw [generatedNinth_lower_spin_tensor_post_label_block,
    generatedNinth_lower_spin_tensor_post_sign_block,
    generatedNinth_lower_spin_tensor_packed_coordinate_block]
  intro b
  fin_cases b <;>
    norm_num only [generatedNinthLowerSpinTensorStageWords,
      generatedNinthLowerSpinTensorStageWords10,
      generatedNinthLowerSpinTensorPostLabelWords, generatedNinthLowerSpinTensorPostSignWords,
      generatedNinthLowerSpinTensorSpatialDenominator, generatedNinthLowerSpinTensorInputWords]
  all_goals decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete normalized integer circuit stage on a single source column.
private theorem column_19 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorPostInteger 10
      (fun m => generatedNinthLowerSpinTensorStageInteger 10 5 m 19) n =
        (generatedNinthLowerSpinTensorSpatialDenominator 10 : ℤ) *
          generatedNinthLowerSpinTensorInputInteger n 19 := by
  apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
  change ∀ b : Fin 16, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorPostInteger 10
      (fun m => generatedNinthLowerSpinTensorStageInteger 10 5 m 19)
        (generatedNinthLowerSpinTensorBlockIndex b u) =
      (generatedNinthLowerSpinTensorSpatialDenominator 10 : ℤ) *
        generatedNinthLowerSpinTensorInputInteger (generatedNinthLowerSpinTensorBlockIndex b u) 19
  dsimp only [generatedNinthLowerSpinTensorPostInteger,
    generatedNinthLowerSpinTensorStageInteger, generatedNinthLowerSpinTensorInputInteger]
  simp_rw [generatedNinth_lower_spin_tensor_post_label_block,
    generatedNinth_lower_spin_tensor_post_sign_block,
    generatedNinth_lower_spin_tensor_packed_coordinate_block]
  intro b
  fin_cases b <;>
    norm_num only [generatedNinthLowerSpinTensorStageWords,
      generatedNinthLowerSpinTensorStageWords10,
      generatedNinthLowerSpinTensorPostLabelWords, generatedNinthLowerSpinTensorPostSignWords,
      generatedNinthLowerSpinTensorSpatialDenominator, generatedNinthLowerSpinTensorInputWords]
  all_goals decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete normalized integer circuit stage on a single source column.
private theorem column_20 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorPostInteger 10
      (fun m => generatedNinthLowerSpinTensorStageInteger 10 5 m 20) n =
        (generatedNinthLowerSpinTensorSpatialDenominator 10 : ℤ) *
          generatedNinthLowerSpinTensorInputInteger n 20 := by
  apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
  change ∀ b : Fin 16, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorPostInteger 10
      (fun m => generatedNinthLowerSpinTensorStageInteger 10 5 m 20)
        (generatedNinthLowerSpinTensorBlockIndex b u) =
      (generatedNinthLowerSpinTensorSpatialDenominator 10 : ℤ) *
        generatedNinthLowerSpinTensorInputInteger (generatedNinthLowerSpinTensorBlockIndex b u) 20
  dsimp only [generatedNinthLowerSpinTensorPostInteger,
    generatedNinthLowerSpinTensorStageInteger, generatedNinthLowerSpinTensorInputInteger]
  simp_rw [generatedNinth_lower_spin_tensor_post_label_block,
    generatedNinth_lower_spin_tensor_post_sign_block,
    generatedNinth_lower_spin_tensor_packed_coordinate_block]
  intro b
  fin_cases b <;>
    norm_num only [generatedNinthLowerSpinTensorStageWords,
      generatedNinthLowerSpinTensorStageWords10,
      generatedNinthLowerSpinTensorPostLabelWords, generatedNinthLowerSpinTensorPostSignWords,
      generatedNinthLowerSpinTensorSpatialDenominator, generatedNinthLowerSpinTensorInputWords]
  all_goals decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete normalized integer circuit stage on a single source column.
private theorem column_21 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorPostInteger 10
      (fun m => generatedNinthLowerSpinTensorStageInteger 10 5 m 21) n =
        (generatedNinthLowerSpinTensorSpatialDenominator 10 : ℤ) *
          generatedNinthLowerSpinTensorInputInteger n 21 := by
  apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
  change ∀ b : Fin 16, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorPostInteger 10
      (fun m => generatedNinthLowerSpinTensorStageInteger 10 5 m 21)
        (generatedNinthLowerSpinTensorBlockIndex b u) =
      (generatedNinthLowerSpinTensorSpatialDenominator 10 : ℤ) *
        generatedNinthLowerSpinTensorInputInteger (generatedNinthLowerSpinTensorBlockIndex b u) 21
  dsimp only [generatedNinthLowerSpinTensorPostInteger,
    generatedNinthLowerSpinTensorStageInteger, generatedNinthLowerSpinTensorInputInteger]
  simp_rw [generatedNinth_lower_spin_tensor_post_label_block,
    generatedNinth_lower_spin_tensor_post_sign_block,
    generatedNinth_lower_spin_tensor_packed_coordinate_block]
  intro b
  fin_cases b <;>
    norm_num only [generatedNinthLowerSpinTensorStageWords,
      generatedNinthLowerSpinTensorStageWords10,
      generatedNinthLowerSpinTensorPostLabelWords, generatedNinthLowerSpinTensorPostSignWords,
      generatedNinthLowerSpinTensorSpatialDenominator, generatedNinthLowerSpinTensorInputWords]
  all_goals decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete normalized integer circuit stage on a single source column.
private theorem column_22 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorPostInteger 10
      (fun m => generatedNinthLowerSpinTensorStageInteger 10 5 m 22) n =
        (generatedNinthLowerSpinTensorSpatialDenominator 10 : ℤ) *
          generatedNinthLowerSpinTensorInputInteger n 22 := by
  apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
  change ∀ b : Fin 16, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorPostInteger 10
      (fun m => generatedNinthLowerSpinTensorStageInteger 10 5 m 22)
        (generatedNinthLowerSpinTensorBlockIndex b u) =
      (generatedNinthLowerSpinTensorSpatialDenominator 10 : ℤ) *
        generatedNinthLowerSpinTensorInputInteger (generatedNinthLowerSpinTensorBlockIndex b u) 22
  dsimp only [generatedNinthLowerSpinTensorPostInteger,
    generatedNinthLowerSpinTensorStageInteger, generatedNinthLowerSpinTensorInputInteger]
  simp_rw [generatedNinth_lower_spin_tensor_post_label_block,
    generatedNinth_lower_spin_tensor_post_sign_block,
    generatedNinth_lower_spin_tensor_packed_coordinate_block]
  intro b
  fin_cases b <;>
    norm_num only [generatedNinthLowerSpinTensorStageWords,
      generatedNinthLowerSpinTensorStageWords10,
      generatedNinthLowerSpinTensorPostLabelWords, generatedNinthLowerSpinTensorPostSignWords,
      generatedNinthLowerSpinTensorSpatialDenominator, generatedNinthLowerSpinTensorInputWords]
  all_goals decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete normalized integer circuit stage on a single source column.
private theorem column_23 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorPostInteger 10
      (fun m => generatedNinthLowerSpinTensorStageInteger 10 5 m 23) n =
        (generatedNinthLowerSpinTensorSpatialDenominator 10 : ℤ) *
          generatedNinthLowerSpinTensorInputInteger n 23 := by
  apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
  change ∀ b : Fin 16, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorPostInteger 10
      (fun m => generatedNinthLowerSpinTensorStageInteger 10 5 m 23)
        (generatedNinthLowerSpinTensorBlockIndex b u) =
      (generatedNinthLowerSpinTensorSpatialDenominator 10 : ℤ) *
        generatedNinthLowerSpinTensorInputInteger (generatedNinthLowerSpinTensorBlockIndex b u) 23
  dsimp only [generatedNinthLowerSpinTensorPostInteger,
    generatedNinthLowerSpinTensorStageInteger, generatedNinthLowerSpinTensorInputInteger]
  simp_rw [generatedNinth_lower_spin_tensor_post_label_block,
    generatedNinth_lower_spin_tensor_post_sign_block,
    generatedNinth_lower_spin_tensor_packed_coordinate_block]
  intro b
  fin_cases b <;>
    norm_num only [generatedNinthLowerSpinTensorStageWords,
      generatedNinthLowerSpinTensorStageWords10,
      generatedNinthLowerSpinTensorPostLabelWords, generatedNinthLowerSpinTensorPostSignWords,
      generatedNinthLowerSpinTensorSpatialDenominator, generatedNinthLowerSpinTensorInputWords]
  all_goals decide +kernel

/-- Every original tensor column has all 4096 exact packet coordinates. -/
theorem generatedNinth_lower_spin_tensor_replay_packet_10_finish : ∀ (j : Fin 24) (n : Fin 4096),
    generatedNinthLowerSpinTensorPostInteger 10
      (fun m => generatedNinthLowerSpinTensorStageInteger 10 5 m j) n =
        (generatedNinthLowerSpinTensorSpatialDenominator 10 : ℤ) *
          generatedNinthLowerSpinTensorInputInteger n j := by
  intro j n
  fin_cases j
  · exact column_00 n
  · exact column_01 n
  · exact column_02 n
  · exact column_03 n
  · exact column_04 n
  · exact column_05 n
  · exact column_06 n
  · exact column_07 n
  · exact column_08 n
  · exact column_09 n
  · exact column_10 n
  · exact column_11 n
  · exact column_12 n
  · exact column_13 n
  · exact column_14 n
  · exact column_15 n
  · exact column_16 n
  · exact column_17 n
  · exact column_18 n
  · exact column_19 n
  · exact column_20 n
  · exact column_21 n
  · exact column_22 n
  · exact column_23 n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
