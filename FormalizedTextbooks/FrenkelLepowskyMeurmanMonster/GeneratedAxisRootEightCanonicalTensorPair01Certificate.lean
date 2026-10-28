/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalTensorStageBlocks

/-! All complete original canonical coordinates of one genuine Fourier pair. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

set_option maxHeartbeats 64000000 in
-- Replay all twenty-four complete physical columns from their exact fixed source rows.
private theorem block_00 : ∀ r : Fin 24, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (4 : Fin 8))
      (generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (5 : Fin 8))
        (generatedRootEightCanonicalTensorStageInteger 1 r))
          (generatedNinthLowerSpinTensorBlockIndex 0 u) =
      2 * generatedRootEightCanonicalTensorStageInteger 2 r
        (generatedNinthLowerSpinTensorBlockIndex 0 u) := by
  simp_rw [generatedRootEight_tensor_fourier_pair_block (4 : Fin 8) 5,
    generatedRootEight_canonical_tensor_stage_block]
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Replay all twenty-four complete physical columns from their exact fixed source rows.
private theorem block_01 : ∀ r : Fin 24, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (4 : Fin 8))
      (generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (5 : Fin 8))
        (generatedRootEightCanonicalTensorStageInteger 1 r))
          (generatedNinthLowerSpinTensorBlockIndex 1 u) =
      2 * generatedRootEightCanonicalTensorStageInteger 2 r
        (generatedNinthLowerSpinTensorBlockIndex 1 u) := by
  simp_rw [generatedRootEight_tensor_fourier_pair_block (4 : Fin 8) 5,
    generatedRootEight_canonical_tensor_stage_block]
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Replay all twenty-four complete physical columns from their exact fixed source rows.
private theorem block_02 : ∀ r : Fin 24, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (4 : Fin 8))
      (generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (5 : Fin 8))
        (generatedRootEightCanonicalTensorStageInteger 1 r))
          (generatedNinthLowerSpinTensorBlockIndex 2 u) =
      2 * generatedRootEightCanonicalTensorStageInteger 2 r
        (generatedNinthLowerSpinTensorBlockIndex 2 u) := by
  simp_rw [generatedRootEight_tensor_fourier_pair_block (4 : Fin 8) 5,
    generatedRootEight_canonical_tensor_stage_block]
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Replay all twenty-four complete physical columns from their exact fixed source rows.
private theorem block_03 : ∀ r : Fin 24, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (4 : Fin 8))
      (generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (5 : Fin 8))
        (generatedRootEightCanonicalTensorStageInteger 1 r))
          (generatedNinthLowerSpinTensorBlockIndex 3 u) =
      2 * generatedRootEightCanonicalTensorStageInteger 2 r
        (generatedNinthLowerSpinTensorBlockIndex 3 u) := by
  simp_rw [generatedRootEight_tensor_fourier_pair_block (4 : Fin 8) 5,
    generatedRootEight_canonical_tensor_stage_block]
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Replay all twenty-four complete physical columns from their exact fixed source rows.
private theorem block_04 : ∀ r : Fin 24, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (4 : Fin 8))
      (generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (5 : Fin 8))
        (generatedRootEightCanonicalTensorStageInteger 1 r))
          (generatedNinthLowerSpinTensorBlockIndex 4 u) =
      2 * generatedRootEightCanonicalTensorStageInteger 2 r
        (generatedNinthLowerSpinTensorBlockIndex 4 u) := by
  simp_rw [generatedRootEight_tensor_fourier_pair_block (4 : Fin 8) 5,
    generatedRootEight_canonical_tensor_stage_block]
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Replay all twenty-four complete physical columns from their exact fixed source rows.
private theorem block_05 : ∀ r : Fin 24, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (4 : Fin 8))
      (generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (5 : Fin 8))
        (generatedRootEightCanonicalTensorStageInteger 1 r))
          (generatedNinthLowerSpinTensorBlockIndex 5 u) =
      2 * generatedRootEightCanonicalTensorStageInteger 2 r
        (generatedNinthLowerSpinTensorBlockIndex 5 u) := by
  simp_rw [generatedRootEight_tensor_fourier_pair_block (4 : Fin 8) 5,
    generatedRootEight_canonical_tensor_stage_block]
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Replay all twenty-four complete physical columns from their exact fixed source rows.
private theorem block_06 : ∀ r : Fin 24, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (4 : Fin 8))
      (generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (5 : Fin 8))
        (generatedRootEightCanonicalTensorStageInteger 1 r))
          (generatedNinthLowerSpinTensorBlockIndex 6 u) =
      2 * generatedRootEightCanonicalTensorStageInteger 2 r
        (generatedNinthLowerSpinTensorBlockIndex 6 u) := by
  simp_rw [generatedRootEight_tensor_fourier_pair_block (4 : Fin 8) 5,
    generatedRootEight_canonical_tensor_stage_block]
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Replay all twenty-four complete physical columns from their exact fixed source rows.
private theorem block_07 : ∀ r : Fin 24, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (4 : Fin 8))
      (generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (5 : Fin 8))
        (generatedRootEightCanonicalTensorStageInteger 1 r))
          (generatedNinthLowerSpinTensorBlockIndex 7 u) =
      2 * generatedRootEightCanonicalTensorStageInteger 2 r
        (generatedNinthLowerSpinTensorBlockIndex 7 u) := by
  simp_rw [generatedRootEight_tensor_fourier_pair_block (4 : Fin 8) 5,
    generatedRootEight_canonical_tensor_stage_block]
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Replay all twenty-four complete physical columns from their exact fixed source rows.
private theorem block_08 : ∀ r : Fin 24, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (4 : Fin 8))
      (generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (5 : Fin 8))
        (generatedRootEightCanonicalTensorStageInteger 1 r))
          (generatedNinthLowerSpinTensorBlockIndex 8 u) =
      2 * generatedRootEightCanonicalTensorStageInteger 2 r
        (generatedNinthLowerSpinTensorBlockIndex 8 u) := by
  simp_rw [generatedRootEight_tensor_fourier_pair_block (4 : Fin 8) 5,
    generatedRootEight_canonical_tensor_stage_block]
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Replay all twenty-four complete physical columns from their exact fixed source rows.
private theorem block_09 : ∀ r : Fin 24, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (4 : Fin 8))
      (generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (5 : Fin 8))
        (generatedRootEightCanonicalTensorStageInteger 1 r))
          (generatedNinthLowerSpinTensorBlockIndex 9 u) =
      2 * generatedRootEightCanonicalTensorStageInteger 2 r
        (generatedNinthLowerSpinTensorBlockIndex 9 u) := by
  simp_rw [generatedRootEight_tensor_fourier_pair_block (4 : Fin 8) 5,
    generatedRootEight_canonical_tensor_stage_block]
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Replay all twenty-four complete physical columns from their exact fixed source rows.
private theorem block_10 : ∀ r : Fin 24, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (4 : Fin 8))
      (generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (5 : Fin 8))
        (generatedRootEightCanonicalTensorStageInteger 1 r))
          (generatedNinthLowerSpinTensorBlockIndex 10 u) =
      2 * generatedRootEightCanonicalTensorStageInteger 2 r
        (generatedNinthLowerSpinTensorBlockIndex 10 u) := by
  simp_rw [generatedRootEight_tensor_fourier_pair_block (4 : Fin 8) 5,
    generatedRootEight_canonical_tensor_stage_block]
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Replay all twenty-four complete physical columns from their exact fixed source rows.
private theorem block_11 : ∀ r : Fin 24, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (4 : Fin 8))
      (generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (5 : Fin 8))
        (generatedRootEightCanonicalTensorStageInteger 1 r))
          (generatedNinthLowerSpinTensorBlockIndex 11 u) =
      2 * generatedRootEightCanonicalTensorStageInteger 2 r
        (generatedNinthLowerSpinTensorBlockIndex 11 u) := by
  simp_rw [generatedRootEight_tensor_fourier_pair_block (4 : Fin 8) 5,
    generatedRootEight_canonical_tensor_stage_block]
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Replay all twenty-four complete physical columns from their exact fixed source rows.
private theorem block_12 : ∀ r : Fin 24, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (4 : Fin 8))
      (generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (5 : Fin 8))
        (generatedRootEightCanonicalTensorStageInteger 1 r))
          (generatedNinthLowerSpinTensorBlockIndex 12 u) =
      2 * generatedRootEightCanonicalTensorStageInteger 2 r
        (generatedNinthLowerSpinTensorBlockIndex 12 u) := by
  simp_rw [generatedRootEight_tensor_fourier_pair_block (4 : Fin 8) 5,
    generatedRootEight_canonical_tensor_stage_block]
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Replay all twenty-four complete physical columns from their exact fixed source rows.
private theorem block_13 : ∀ r : Fin 24, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (4 : Fin 8))
      (generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (5 : Fin 8))
        (generatedRootEightCanonicalTensorStageInteger 1 r))
          (generatedNinthLowerSpinTensorBlockIndex 13 u) =
      2 * generatedRootEightCanonicalTensorStageInteger 2 r
        (generatedNinthLowerSpinTensorBlockIndex 13 u) := by
  simp_rw [generatedRootEight_tensor_fourier_pair_block (4 : Fin 8) 5,
    generatedRootEight_canonical_tensor_stage_block]
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Replay all twenty-four complete physical columns from their exact fixed source rows.
private theorem block_14 : ∀ r : Fin 24, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (4 : Fin 8))
      (generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (5 : Fin 8))
        (generatedRootEightCanonicalTensorStageInteger 1 r))
          (generatedNinthLowerSpinTensorBlockIndex 14 u) =
      2 * generatedRootEightCanonicalTensorStageInteger 2 r
        (generatedNinthLowerSpinTensorBlockIndex 14 u) := by
  simp_rw [generatedRootEight_tensor_fourier_pair_block (4 : Fin 8) 5,
    generatedRootEight_canonical_tensor_stage_block]
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Replay all twenty-four complete physical columns from their exact fixed source rows.
private theorem block_15 : ∀ r : Fin 24, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (4 : Fin 8))
      (generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (5 : Fin 8))
        (generatedRootEightCanonicalTensorStageInteger 1 r))
          (generatedNinthLowerSpinTensorBlockIndex 15 u) =
      2 * generatedRootEightCanonicalTensorStageInteger 2 r
        (generatedNinthLowerSpinTensorBlockIndex 15 u) := by
  simp_rw [generatedRootEight_tensor_fourier_pair_block (4 : Fin 8) 5,
    generatedRootEight_canonical_tensor_stage_block]
  decide +kernel

/-- Every complete bounded canonical block has its genuine full-pair certificate. -/
theorem generatedRootEight_canonical_tensor_pair_01_blocks : ∀ b : Fin 16, ∀ r : Fin 24, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (4 : Fin 8))
      (generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (5 : Fin 8))
        (generatedRootEightCanonicalTensorStageInteger 1 r))
          (generatedNinthLowerSpinTensorBlockIndex b u) =
      2 * generatedRootEightCanonicalTensorStageInteger 2 r
        (generatedNinthLowerSpinTensorBlockIndex b u) := by
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
