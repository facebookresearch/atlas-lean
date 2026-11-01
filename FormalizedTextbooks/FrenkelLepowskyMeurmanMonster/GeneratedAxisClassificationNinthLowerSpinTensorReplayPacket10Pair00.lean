/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinTensorBlockFourier

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinTensorCircuitData

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinTensorBoundedQuantifier

/-! Full 4096-coordinate column packets for generator 10 pair00. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
-- Check one complete normalized integer circuit stage on a single source column.
private theorem column_00 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorFourierInteger 8
      (generatedNinthLowerSpinTensorFourierInteger 9
        (fun m => generatedNinthLowerSpinTensorStageInteger 10 0 m 0)) n =
          2 * generatedNinthLowerSpinTensorStageInteger 10 1 n 0 := by
  apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
  change ∀ b : Fin 16, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger 8
      (generatedNinthLowerSpinTensorFourierInteger 9
        (fun m => generatedNinthLowerSpinTensorStageInteger 10 0 m 0))
          (generatedNinthLowerSpinTensorBlockIndex b u) =
            2 * generatedNinthLowerSpinTensorStageInteger 10 1
              (generatedNinthLowerSpinTensorBlockIndex b u) 0
  simp_rw [generatedNinth_lower_spin_tensor_fourier_pair_block]
  dsimp only [generatedNinthLowerSpinTensorStageInteger]
  simp_rw [generatedNinth_lower_spin_tensor_packed_coordinate_block]
  intro b
  fin_cases b <;>
    norm_num only [generatedNinthLowerSpinTensorBlockFourier,
      generatedNinthLowerSpinTensorBlockXorHigh, generatedNinthLowerSpinTensorBlockXorLow,
      generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  all_goals decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete normalized integer circuit stage on a single source column.
private theorem column_01 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorFourierInteger 8
      (generatedNinthLowerSpinTensorFourierInteger 9
        (fun m => generatedNinthLowerSpinTensorStageInteger 10 0 m 1)) n =
          2 * generatedNinthLowerSpinTensorStageInteger 10 1 n 1 := by
  apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
  change ∀ b : Fin 16, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger 8
      (generatedNinthLowerSpinTensorFourierInteger 9
        (fun m => generatedNinthLowerSpinTensorStageInteger 10 0 m 1))
          (generatedNinthLowerSpinTensorBlockIndex b u) =
            2 * generatedNinthLowerSpinTensorStageInteger 10 1
              (generatedNinthLowerSpinTensorBlockIndex b u) 1
  simp_rw [generatedNinth_lower_spin_tensor_fourier_pair_block]
  dsimp only [generatedNinthLowerSpinTensorStageInteger]
  simp_rw [generatedNinth_lower_spin_tensor_packed_coordinate_block]
  intro b
  fin_cases b <;>
    norm_num only [generatedNinthLowerSpinTensorBlockFourier,
      generatedNinthLowerSpinTensorBlockXorHigh, generatedNinthLowerSpinTensorBlockXorLow,
      generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  all_goals decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete normalized integer circuit stage on a single source column.
private theorem column_02 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorFourierInteger 8
      (generatedNinthLowerSpinTensorFourierInteger 9
        (fun m => generatedNinthLowerSpinTensorStageInteger 10 0 m 2)) n =
          2 * generatedNinthLowerSpinTensorStageInteger 10 1 n 2 := by
  apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
  change ∀ b : Fin 16, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger 8
      (generatedNinthLowerSpinTensorFourierInteger 9
        (fun m => generatedNinthLowerSpinTensorStageInteger 10 0 m 2))
          (generatedNinthLowerSpinTensorBlockIndex b u) =
            2 * generatedNinthLowerSpinTensorStageInteger 10 1
              (generatedNinthLowerSpinTensorBlockIndex b u) 2
  simp_rw [generatedNinth_lower_spin_tensor_fourier_pair_block]
  dsimp only [generatedNinthLowerSpinTensorStageInteger]
  simp_rw [generatedNinth_lower_spin_tensor_packed_coordinate_block]
  intro b
  fin_cases b <;>
    norm_num only [generatedNinthLowerSpinTensorBlockFourier,
      generatedNinthLowerSpinTensorBlockXorHigh, generatedNinthLowerSpinTensorBlockXorLow,
      generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  all_goals decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete normalized integer circuit stage on a single source column.
private theorem column_03 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorFourierInteger 8
      (generatedNinthLowerSpinTensorFourierInteger 9
        (fun m => generatedNinthLowerSpinTensorStageInteger 10 0 m 3)) n =
          2 * generatedNinthLowerSpinTensorStageInteger 10 1 n 3 := by
  apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
  change ∀ b : Fin 16, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger 8
      (generatedNinthLowerSpinTensorFourierInteger 9
        (fun m => generatedNinthLowerSpinTensorStageInteger 10 0 m 3))
          (generatedNinthLowerSpinTensorBlockIndex b u) =
            2 * generatedNinthLowerSpinTensorStageInteger 10 1
              (generatedNinthLowerSpinTensorBlockIndex b u) 3
  simp_rw [generatedNinth_lower_spin_tensor_fourier_pair_block]
  dsimp only [generatedNinthLowerSpinTensorStageInteger]
  simp_rw [generatedNinth_lower_spin_tensor_packed_coordinate_block]
  intro b
  fin_cases b <;>
    norm_num only [generatedNinthLowerSpinTensorBlockFourier,
      generatedNinthLowerSpinTensorBlockXorHigh, generatedNinthLowerSpinTensorBlockXorLow,
      generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  all_goals decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete normalized integer circuit stage on a single source column.
private theorem column_04 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorFourierInteger 8
      (generatedNinthLowerSpinTensorFourierInteger 9
        (fun m => generatedNinthLowerSpinTensorStageInteger 10 0 m 4)) n =
          2 * generatedNinthLowerSpinTensorStageInteger 10 1 n 4 := by
  apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
  change ∀ b : Fin 16, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger 8
      (generatedNinthLowerSpinTensorFourierInteger 9
        (fun m => generatedNinthLowerSpinTensorStageInteger 10 0 m 4))
          (generatedNinthLowerSpinTensorBlockIndex b u) =
            2 * generatedNinthLowerSpinTensorStageInteger 10 1
              (generatedNinthLowerSpinTensorBlockIndex b u) 4
  simp_rw [generatedNinth_lower_spin_tensor_fourier_pair_block]
  dsimp only [generatedNinthLowerSpinTensorStageInteger]
  simp_rw [generatedNinth_lower_spin_tensor_packed_coordinate_block]
  intro b
  fin_cases b <;>
    norm_num only [generatedNinthLowerSpinTensorBlockFourier,
      generatedNinthLowerSpinTensorBlockXorHigh, generatedNinthLowerSpinTensorBlockXorLow,
      generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  all_goals decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete normalized integer circuit stage on a single source column.
private theorem column_05 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorFourierInteger 8
      (generatedNinthLowerSpinTensorFourierInteger 9
        (fun m => generatedNinthLowerSpinTensorStageInteger 10 0 m 5)) n =
          2 * generatedNinthLowerSpinTensorStageInteger 10 1 n 5 := by
  apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
  change ∀ b : Fin 16, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger 8
      (generatedNinthLowerSpinTensorFourierInteger 9
        (fun m => generatedNinthLowerSpinTensorStageInteger 10 0 m 5))
          (generatedNinthLowerSpinTensorBlockIndex b u) =
            2 * generatedNinthLowerSpinTensorStageInteger 10 1
              (generatedNinthLowerSpinTensorBlockIndex b u) 5
  simp_rw [generatedNinth_lower_spin_tensor_fourier_pair_block]
  dsimp only [generatedNinthLowerSpinTensorStageInteger]
  simp_rw [generatedNinth_lower_spin_tensor_packed_coordinate_block]
  intro b
  fin_cases b <;>
    norm_num only [generatedNinthLowerSpinTensorBlockFourier,
      generatedNinthLowerSpinTensorBlockXorHigh, generatedNinthLowerSpinTensorBlockXorLow,
      generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  all_goals decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete normalized integer circuit stage on a single source column.
private theorem column_06 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorFourierInteger 8
      (generatedNinthLowerSpinTensorFourierInteger 9
        (fun m => generatedNinthLowerSpinTensorStageInteger 10 0 m 6)) n =
          2 * generatedNinthLowerSpinTensorStageInteger 10 1 n 6 := by
  apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
  change ∀ b : Fin 16, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger 8
      (generatedNinthLowerSpinTensorFourierInteger 9
        (fun m => generatedNinthLowerSpinTensorStageInteger 10 0 m 6))
          (generatedNinthLowerSpinTensorBlockIndex b u) =
            2 * generatedNinthLowerSpinTensorStageInteger 10 1
              (generatedNinthLowerSpinTensorBlockIndex b u) 6
  simp_rw [generatedNinth_lower_spin_tensor_fourier_pair_block]
  dsimp only [generatedNinthLowerSpinTensorStageInteger]
  simp_rw [generatedNinth_lower_spin_tensor_packed_coordinate_block]
  intro b
  fin_cases b <;>
    norm_num only [generatedNinthLowerSpinTensorBlockFourier,
      generatedNinthLowerSpinTensorBlockXorHigh, generatedNinthLowerSpinTensorBlockXorLow,
      generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  all_goals decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete normalized integer circuit stage on a single source column.
private theorem column_07 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorFourierInteger 8
      (generatedNinthLowerSpinTensorFourierInteger 9
        (fun m => generatedNinthLowerSpinTensorStageInteger 10 0 m 7)) n =
          2 * generatedNinthLowerSpinTensorStageInteger 10 1 n 7 := by
  apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
  change ∀ b : Fin 16, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger 8
      (generatedNinthLowerSpinTensorFourierInteger 9
        (fun m => generatedNinthLowerSpinTensorStageInteger 10 0 m 7))
          (generatedNinthLowerSpinTensorBlockIndex b u) =
            2 * generatedNinthLowerSpinTensorStageInteger 10 1
              (generatedNinthLowerSpinTensorBlockIndex b u) 7
  simp_rw [generatedNinth_lower_spin_tensor_fourier_pair_block]
  dsimp only [generatedNinthLowerSpinTensorStageInteger]
  simp_rw [generatedNinth_lower_spin_tensor_packed_coordinate_block]
  intro b
  fin_cases b <;>
    norm_num only [generatedNinthLowerSpinTensorBlockFourier,
      generatedNinthLowerSpinTensorBlockXorHigh, generatedNinthLowerSpinTensorBlockXorLow,
      generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  all_goals decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete normalized integer circuit stage on a single source column.
private theorem column_08 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorFourierInteger 8
      (generatedNinthLowerSpinTensorFourierInteger 9
        (fun m => generatedNinthLowerSpinTensorStageInteger 10 0 m 8)) n =
          2 * generatedNinthLowerSpinTensorStageInteger 10 1 n 8 := by
  apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
  change ∀ b : Fin 16, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger 8
      (generatedNinthLowerSpinTensorFourierInteger 9
        (fun m => generatedNinthLowerSpinTensorStageInteger 10 0 m 8))
          (generatedNinthLowerSpinTensorBlockIndex b u) =
            2 * generatedNinthLowerSpinTensorStageInteger 10 1
              (generatedNinthLowerSpinTensorBlockIndex b u) 8
  simp_rw [generatedNinth_lower_spin_tensor_fourier_pair_block]
  dsimp only [generatedNinthLowerSpinTensorStageInteger]
  simp_rw [generatedNinth_lower_spin_tensor_packed_coordinate_block]
  intro b
  fin_cases b <;>
    norm_num only [generatedNinthLowerSpinTensorBlockFourier,
      generatedNinthLowerSpinTensorBlockXorHigh, generatedNinthLowerSpinTensorBlockXorLow,
      generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  all_goals decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete normalized integer circuit stage on a single source column.
private theorem column_09 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorFourierInteger 8
      (generatedNinthLowerSpinTensorFourierInteger 9
        (fun m => generatedNinthLowerSpinTensorStageInteger 10 0 m 9)) n =
          2 * generatedNinthLowerSpinTensorStageInteger 10 1 n 9 := by
  apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
  change ∀ b : Fin 16, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger 8
      (generatedNinthLowerSpinTensorFourierInteger 9
        (fun m => generatedNinthLowerSpinTensorStageInteger 10 0 m 9))
          (generatedNinthLowerSpinTensorBlockIndex b u) =
            2 * generatedNinthLowerSpinTensorStageInteger 10 1
              (generatedNinthLowerSpinTensorBlockIndex b u) 9
  simp_rw [generatedNinth_lower_spin_tensor_fourier_pair_block]
  dsimp only [generatedNinthLowerSpinTensorStageInteger]
  simp_rw [generatedNinth_lower_spin_tensor_packed_coordinate_block]
  intro b
  fin_cases b <;>
    norm_num only [generatedNinthLowerSpinTensorBlockFourier,
      generatedNinthLowerSpinTensorBlockXorHigh, generatedNinthLowerSpinTensorBlockXorLow,
      generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  all_goals decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete normalized integer circuit stage on a single source column.
private theorem column_10 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorFourierInteger 8
      (generatedNinthLowerSpinTensorFourierInteger 9
        (fun m => generatedNinthLowerSpinTensorStageInteger 10 0 m 10)) n =
          2 * generatedNinthLowerSpinTensorStageInteger 10 1 n 10 := by
  apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
  change ∀ b : Fin 16, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger 8
      (generatedNinthLowerSpinTensorFourierInteger 9
        (fun m => generatedNinthLowerSpinTensorStageInteger 10 0 m 10))
          (generatedNinthLowerSpinTensorBlockIndex b u) =
            2 * generatedNinthLowerSpinTensorStageInteger 10 1
              (generatedNinthLowerSpinTensorBlockIndex b u) 10
  simp_rw [generatedNinth_lower_spin_tensor_fourier_pair_block]
  dsimp only [generatedNinthLowerSpinTensorStageInteger]
  simp_rw [generatedNinth_lower_spin_tensor_packed_coordinate_block]
  intro b
  fin_cases b <;>
    norm_num only [generatedNinthLowerSpinTensorBlockFourier,
      generatedNinthLowerSpinTensorBlockXorHigh, generatedNinthLowerSpinTensorBlockXorLow,
      generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  all_goals decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete normalized integer circuit stage on a single source column.
private theorem column_11 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorFourierInteger 8
      (generatedNinthLowerSpinTensorFourierInteger 9
        (fun m => generatedNinthLowerSpinTensorStageInteger 10 0 m 11)) n =
          2 * generatedNinthLowerSpinTensorStageInteger 10 1 n 11 := by
  apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
  change ∀ b : Fin 16, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger 8
      (generatedNinthLowerSpinTensorFourierInteger 9
        (fun m => generatedNinthLowerSpinTensorStageInteger 10 0 m 11))
          (generatedNinthLowerSpinTensorBlockIndex b u) =
            2 * generatedNinthLowerSpinTensorStageInteger 10 1
              (generatedNinthLowerSpinTensorBlockIndex b u) 11
  simp_rw [generatedNinth_lower_spin_tensor_fourier_pair_block]
  dsimp only [generatedNinthLowerSpinTensorStageInteger]
  simp_rw [generatedNinth_lower_spin_tensor_packed_coordinate_block]
  intro b
  fin_cases b <;>
    norm_num only [generatedNinthLowerSpinTensorBlockFourier,
      generatedNinthLowerSpinTensorBlockXorHigh, generatedNinthLowerSpinTensorBlockXorLow,
      generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  all_goals decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete normalized integer circuit stage on a single source column.
private theorem column_12 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorFourierInteger 8
      (generatedNinthLowerSpinTensorFourierInteger 9
        (fun m => generatedNinthLowerSpinTensorStageInteger 10 0 m 12)) n =
          2 * generatedNinthLowerSpinTensorStageInteger 10 1 n 12 := by
  apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
  change ∀ b : Fin 16, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger 8
      (generatedNinthLowerSpinTensorFourierInteger 9
        (fun m => generatedNinthLowerSpinTensorStageInteger 10 0 m 12))
          (generatedNinthLowerSpinTensorBlockIndex b u) =
            2 * generatedNinthLowerSpinTensorStageInteger 10 1
              (generatedNinthLowerSpinTensorBlockIndex b u) 12
  simp_rw [generatedNinth_lower_spin_tensor_fourier_pair_block]
  dsimp only [generatedNinthLowerSpinTensorStageInteger]
  simp_rw [generatedNinth_lower_spin_tensor_packed_coordinate_block]
  intro b
  fin_cases b <;>
    norm_num only [generatedNinthLowerSpinTensorBlockFourier,
      generatedNinthLowerSpinTensorBlockXorHigh, generatedNinthLowerSpinTensorBlockXorLow,
      generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  all_goals decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete normalized integer circuit stage on a single source column.
private theorem column_13 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorFourierInteger 8
      (generatedNinthLowerSpinTensorFourierInteger 9
        (fun m => generatedNinthLowerSpinTensorStageInteger 10 0 m 13)) n =
          2 * generatedNinthLowerSpinTensorStageInteger 10 1 n 13 := by
  apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
  change ∀ b : Fin 16, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger 8
      (generatedNinthLowerSpinTensorFourierInteger 9
        (fun m => generatedNinthLowerSpinTensorStageInteger 10 0 m 13))
          (generatedNinthLowerSpinTensorBlockIndex b u) =
            2 * generatedNinthLowerSpinTensorStageInteger 10 1
              (generatedNinthLowerSpinTensorBlockIndex b u) 13
  simp_rw [generatedNinth_lower_spin_tensor_fourier_pair_block]
  dsimp only [generatedNinthLowerSpinTensorStageInteger]
  simp_rw [generatedNinth_lower_spin_tensor_packed_coordinate_block]
  intro b
  fin_cases b <;>
    norm_num only [generatedNinthLowerSpinTensorBlockFourier,
      generatedNinthLowerSpinTensorBlockXorHigh, generatedNinthLowerSpinTensorBlockXorLow,
      generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  all_goals decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete normalized integer circuit stage on a single source column.
private theorem column_14 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorFourierInteger 8
      (generatedNinthLowerSpinTensorFourierInteger 9
        (fun m => generatedNinthLowerSpinTensorStageInteger 10 0 m 14)) n =
          2 * generatedNinthLowerSpinTensorStageInteger 10 1 n 14 := by
  apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
  change ∀ b : Fin 16, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger 8
      (generatedNinthLowerSpinTensorFourierInteger 9
        (fun m => generatedNinthLowerSpinTensorStageInteger 10 0 m 14))
          (generatedNinthLowerSpinTensorBlockIndex b u) =
            2 * generatedNinthLowerSpinTensorStageInteger 10 1
              (generatedNinthLowerSpinTensorBlockIndex b u) 14
  simp_rw [generatedNinth_lower_spin_tensor_fourier_pair_block]
  dsimp only [generatedNinthLowerSpinTensorStageInteger]
  simp_rw [generatedNinth_lower_spin_tensor_packed_coordinate_block]
  intro b
  fin_cases b <;>
    norm_num only [generatedNinthLowerSpinTensorBlockFourier,
      generatedNinthLowerSpinTensorBlockXorHigh, generatedNinthLowerSpinTensorBlockXorLow,
      generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  all_goals decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete normalized integer circuit stage on a single source column.
private theorem column_15 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorFourierInteger 8
      (generatedNinthLowerSpinTensorFourierInteger 9
        (fun m => generatedNinthLowerSpinTensorStageInteger 10 0 m 15)) n =
          2 * generatedNinthLowerSpinTensorStageInteger 10 1 n 15 := by
  apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
  change ∀ b : Fin 16, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger 8
      (generatedNinthLowerSpinTensorFourierInteger 9
        (fun m => generatedNinthLowerSpinTensorStageInteger 10 0 m 15))
          (generatedNinthLowerSpinTensorBlockIndex b u) =
            2 * generatedNinthLowerSpinTensorStageInteger 10 1
              (generatedNinthLowerSpinTensorBlockIndex b u) 15
  simp_rw [generatedNinth_lower_spin_tensor_fourier_pair_block]
  dsimp only [generatedNinthLowerSpinTensorStageInteger]
  simp_rw [generatedNinth_lower_spin_tensor_packed_coordinate_block]
  intro b
  fin_cases b <;>
    norm_num only [generatedNinthLowerSpinTensorBlockFourier,
      generatedNinthLowerSpinTensorBlockXorHigh, generatedNinthLowerSpinTensorBlockXorLow,
      generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  all_goals decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete normalized integer circuit stage on a single source column.
private theorem column_16 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorFourierInteger 8
      (generatedNinthLowerSpinTensorFourierInteger 9
        (fun m => generatedNinthLowerSpinTensorStageInteger 10 0 m 16)) n =
          2 * generatedNinthLowerSpinTensorStageInteger 10 1 n 16 := by
  apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
  change ∀ b : Fin 16, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger 8
      (generatedNinthLowerSpinTensorFourierInteger 9
        (fun m => generatedNinthLowerSpinTensorStageInteger 10 0 m 16))
          (generatedNinthLowerSpinTensorBlockIndex b u) =
            2 * generatedNinthLowerSpinTensorStageInteger 10 1
              (generatedNinthLowerSpinTensorBlockIndex b u) 16
  simp_rw [generatedNinth_lower_spin_tensor_fourier_pair_block]
  dsimp only [generatedNinthLowerSpinTensorStageInteger]
  simp_rw [generatedNinth_lower_spin_tensor_packed_coordinate_block]
  intro b
  fin_cases b <;>
    norm_num only [generatedNinthLowerSpinTensorBlockFourier,
      generatedNinthLowerSpinTensorBlockXorHigh, generatedNinthLowerSpinTensorBlockXorLow,
      generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  all_goals decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete normalized integer circuit stage on a single source column.
private theorem column_17 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorFourierInteger 8
      (generatedNinthLowerSpinTensorFourierInteger 9
        (fun m => generatedNinthLowerSpinTensorStageInteger 10 0 m 17)) n =
          2 * generatedNinthLowerSpinTensorStageInteger 10 1 n 17 := by
  apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
  change ∀ b : Fin 16, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger 8
      (generatedNinthLowerSpinTensorFourierInteger 9
        (fun m => generatedNinthLowerSpinTensorStageInteger 10 0 m 17))
          (generatedNinthLowerSpinTensorBlockIndex b u) =
            2 * generatedNinthLowerSpinTensorStageInteger 10 1
              (generatedNinthLowerSpinTensorBlockIndex b u) 17
  simp_rw [generatedNinth_lower_spin_tensor_fourier_pair_block]
  dsimp only [generatedNinthLowerSpinTensorStageInteger]
  simp_rw [generatedNinth_lower_spin_tensor_packed_coordinate_block]
  intro b
  fin_cases b <;>
    norm_num only [generatedNinthLowerSpinTensorBlockFourier,
      generatedNinthLowerSpinTensorBlockXorHigh, generatedNinthLowerSpinTensorBlockXorLow,
      generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  all_goals decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete normalized integer circuit stage on a single source column.
private theorem column_18 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorFourierInteger 8
      (generatedNinthLowerSpinTensorFourierInteger 9
        (fun m => generatedNinthLowerSpinTensorStageInteger 10 0 m 18)) n =
          2 * generatedNinthLowerSpinTensorStageInteger 10 1 n 18 := by
  apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
  change ∀ b : Fin 16, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger 8
      (generatedNinthLowerSpinTensorFourierInteger 9
        (fun m => generatedNinthLowerSpinTensorStageInteger 10 0 m 18))
          (generatedNinthLowerSpinTensorBlockIndex b u) =
            2 * generatedNinthLowerSpinTensorStageInteger 10 1
              (generatedNinthLowerSpinTensorBlockIndex b u) 18
  simp_rw [generatedNinth_lower_spin_tensor_fourier_pair_block]
  dsimp only [generatedNinthLowerSpinTensorStageInteger]
  simp_rw [generatedNinth_lower_spin_tensor_packed_coordinate_block]
  intro b
  fin_cases b <;>
    norm_num only [generatedNinthLowerSpinTensorBlockFourier,
      generatedNinthLowerSpinTensorBlockXorHigh, generatedNinthLowerSpinTensorBlockXorLow,
      generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  all_goals decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete normalized integer circuit stage on a single source column.
private theorem column_19 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorFourierInteger 8
      (generatedNinthLowerSpinTensorFourierInteger 9
        (fun m => generatedNinthLowerSpinTensorStageInteger 10 0 m 19)) n =
          2 * generatedNinthLowerSpinTensorStageInteger 10 1 n 19 := by
  apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
  change ∀ b : Fin 16, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger 8
      (generatedNinthLowerSpinTensorFourierInteger 9
        (fun m => generatedNinthLowerSpinTensorStageInteger 10 0 m 19))
          (generatedNinthLowerSpinTensorBlockIndex b u) =
            2 * generatedNinthLowerSpinTensorStageInteger 10 1
              (generatedNinthLowerSpinTensorBlockIndex b u) 19
  simp_rw [generatedNinth_lower_spin_tensor_fourier_pair_block]
  dsimp only [generatedNinthLowerSpinTensorStageInteger]
  simp_rw [generatedNinth_lower_spin_tensor_packed_coordinate_block]
  intro b
  fin_cases b <;>
    norm_num only [generatedNinthLowerSpinTensorBlockFourier,
      generatedNinthLowerSpinTensorBlockXorHigh, generatedNinthLowerSpinTensorBlockXorLow,
      generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  all_goals decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete normalized integer circuit stage on a single source column.
private theorem column_20 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorFourierInteger 8
      (generatedNinthLowerSpinTensorFourierInteger 9
        (fun m => generatedNinthLowerSpinTensorStageInteger 10 0 m 20)) n =
          2 * generatedNinthLowerSpinTensorStageInteger 10 1 n 20 := by
  apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
  change ∀ b : Fin 16, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger 8
      (generatedNinthLowerSpinTensorFourierInteger 9
        (fun m => generatedNinthLowerSpinTensorStageInteger 10 0 m 20))
          (generatedNinthLowerSpinTensorBlockIndex b u) =
            2 * generatedNinthLowerSpinTensorStageInteger 10 1
              (generatedNinthLowerSpinTensorBlockIndex b u) 20
  simp_rw [generatedNinth_lower_spin_tensor_fourier_pair_block]
  dsimp only [generatedNinthLowerSpinTensorStageInteger]
  simp_rw [generatedNinth_lower_spin_tensor_packed_coordinate_block]
  intro b
  fin_cases b <;>
    norm_num only [generatedNinthLowerSpinTensorBlockFourier,
      generatedNinthLowerSpinTensorBlockXorHigh, generatedNinthLowerSpinTensorBlockXorLow,
      generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  all_goals decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete normalized integer circuit stage on a single source column.
private theorem column_21 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorFourierInteger 8
      (generatedNinthLowerSpinTensorFourierInteger 9
        (fun m => generatedNinthLowerSpinTensorStageInteger 10 0 m 21)) n =
          2 * generatedNinthLowerSpinTensorStageInteger 10 1 n 21 := by
  apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
  change ∀ b : Fin 16, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger 8
      (generatedNinthLowerSpinTensorFourierInteger 9
        (fun m => generatedNinthLowerSpinTensorStageInteger 10 0 m 21))
          (generatedNinthLowerSpinTensorBlockIndex b u) =
            2 * generatedNinthLowerSpinTensorStageInteger 10 1
              (generatedNinthLowerSpinTensorBlockIndex b u) 21
  simp_rw [generatedNinth_lower_spin_tensor_fourier_pair_block]
  dsimp only [generatedNinthLowerSpinTensorStageInteger]
  simp_rw [generatedNinth_lower_spin_tensor_packed_coordinate_block]
  intro b
  fin_cases b <;>
    norm_num only [generatedNinthLowerSpinTensorBlockFourier,
      generatedNinthLowerSpinTensorBlockXorHigh, generatedNinthLowerSpinTensorBlockXorLow,
      generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  all_goals decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete normalized integer circuit stage on a single source column.
private theorem column_22 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorFourierInteger 8
      (generatedNinthLowerSpinTensorFourierInteger 9
        (fun m => generatedNinthLowerSpinTensorStageInteger 10 0 m 22)) n =
          2 * generatedNinthLowerSpinTensorStageInteger 10 1 n 22 := by
  apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
  change ∀ b : Fin 16, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger 8
      (generatedNinthLowerSpinTensorFourierInteger 9
        (fun m => generatedNinthLowerSpinTensorStageInteger 10 0 m 22))
          (generatedNinthLowerSpinTensorBlockIndex b u) =
            2 * generatedNinthLowerSpinTensorStageInteger 10 1
              (generatedNinthLowerSpinTensorBlockIndex b u) 22
  simp_rw [generatedNinth_lower_spin_tensor_fourier_pair_block]
  dsimp only [generatedNinthLowerSpinTensorStageInteger]
  simp_rw [generatedNinth_lower_spin_tensor_packed_coordinate_block]
  intro b
  fin_cases b <;>
    norm_num only [generatedNinthLowerSpinTensorBlockFourier,
      generatedNinthLowerSpinTensorBlockXorHigh, generatedNinthLowerSpinTensorBlockXorLow,
      generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  all_goals decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete normalized integer circuit stage on a single source column.
private theorem column_23 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorFourierInteger 8
      (generatedNinthLowerSpinTensorFourierInteger 9
        (fun m => generatedNinthLowerSpinTensorStageInteger 10 0 m 23)) n =
          2 * generatedNinthLowerSpinTensorStageInteger 10 1 n 23 := by
  apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
  change ∀ b : Fin 16, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger 8
      (generatedNinthLowerSpinTensorFourierInteger 9
        (fun m => generatedNinthLowerSpinTensorStageInteger 10 0 m 23))
          (generatedNinthLowerSpinTensorBlockIndex b u) =
            2 * generatedNinthLowerSpinTensorStageInteger 10 1
              (generatedNinthLowerSpinTensorBlockIndex b u) 23
  simp_rw [generatedNinth_lower_spin_tensor_fourier_pair_block]
  dsimp only [generatedNinthLowerSpinTensorStageInteger]
  simp_rw [generatedNinth_lower_spin_tensor_packed_coordinate_block]
  intro b
  fin_cases b <;>
    norm_num only [generatedNinthLowerSpinTensorBlockFourier,
      generatedNinthLowerSpinTensorBlockXorHigh, generatedNinthLowerSpinTensorBlockXorLow,
      generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  all_goals decide +kernel

/-- Every original tensor column has all 4096 exact packet coordinates. -/
theorem generatedNinth_lower_spin_tensor_replay_packet_10_pair00 : ∀ (j : Fin 24) (n : Fin 4096),
    generatedNinthLowerSpinTensorFourierInteger 8
      (generatedNinthLowerSpinTensorFourierInteger 9
        (fun m => generatedNinthLowerSpinTensorStageInteger 10 0 m j)) n =
          2 * generatedNinthLowerSpinTensorStageInteger 10 1 n j := by
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
