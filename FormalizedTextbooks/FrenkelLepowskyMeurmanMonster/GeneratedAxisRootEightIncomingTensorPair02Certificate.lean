/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingTensorStageBlocks

/-! Full original integer coordinates of chronological Fourier pair 2. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

set_option maxHeartbeats 16000000 in
-- Replay all eight complete source columns using only bounded cached integer coordinates.
private theorem block_00 : ∀ r : Fin 8, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger 2
      (generatedNinthLowerSpinTensorFourierInteger 3
        (generatedRootEightIncomingTensorStageInteger 2 r))
        ⟨0 * 256 + u.val, by omega⟩ =
      2 * generatedRootEightIncomingTensorStageInteger 3 r
        ⟨0 * 256 + u.val, by omega⟩ := by
  change ∀ r : Fin 8, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (2 : Fin 8))
      (generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (3 : Fin 8))
        (generatedRootEightIncomingTensorStageInteger 2 r))
        (generatedNinthLowerSpinTensorBlockIndex 0 u) =
      2 * generatedRootEightIncomingTensorStageInteger 3 r
        (generatedNinthLowerSpinTensorBlockIndex 0 u)
  simp_rw [generatedRootEight_tensor_fourier_pair_block (2 : Fin 8) 3,
    generatedRootEight_incoming_tensor_stage_block]
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Replay all eight complete source columns using only bounded cached integer coordinates.
private theorem block_01 : ∀ r : Fin 8, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger 2
      (generatedNinthLowerSpinTensorFourierInteger 3
        (generatedRootEightIncomingTensorStageInteger 2 r))
        ⟨1 * 256 + u.val, by omega⟩ =
      2 * generatedRootEightIncomingTensorStageInteger 3 r
        ⟨1 * 256 + u.val, by omega⟩ := by
  change ∀ r : Fin 8, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (2 : Fin 8))
      (generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (3 : Fin 8))
        (generatedRootEightIncomingTensorStageInteger 2 r))
        (generatedNinthLowerSpinTensorBlockIndex 1 u) =
      2 * generatedRootEightIncomingTensorStageInteger 3 r
        (generatedNinthLowerSpinTensorBlockIndex 1 u)
  simp_rw [generatedRootEight_tensor_fourier_pair_block (2 : Fin 8) 3,
    generatedRootEight_incoming_tensor_stage_block]
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Replay all eight complete source columns using only bounded cached integer coordinates.
private theorem block_02 : ∀ r : Fin 8, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger 2
      (generatedNinthLowerSpinTensorFourierInteger 3
        (generatedRootEightIncomingTensorStageInteger 2 r))
        ⟨2 * 256 + u.val, by omega⟩ =
      2 * generatedRootEightIncomingTensorStageInteger 3 r
        ⟨2 * 256 + u.val, by omega⟩ := by
  change ∀ r : Fin 8, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (2 : Fin 8))
      (generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (3 : Fin 8))
        (generatedRootEightIncomingTensorStageInteger 2 r))
        (generatedNinthLowerSpinTensorBlockIndex 2 u) =
      2 * generatedRootEightIncomingTensorStageInteger 3 r
        (generatedNinthLowerSpinTensorBlockIndex 2 u)
  simp_rw [generatedRootEight_tensor_fourier_pair_block (2 : Fin 8) 3,
    generatedRootEight_incoming_tensor_stage_block]
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Replay all eight complete source columns using only bounded cached integer coordinates.
private theorem block_03 : ∀ r : Fin 8, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger 2
      (generatedNinthLowerSpinTensorFourierInteger 3
        (generatedRootEightIncomingTensorStageInteger 2 r))
        ⟨3 * 256 + u.val, by omega⟩ =
      2 * generatedRootEightIncomingTensorStageInteger 3 r
        ⟨3 * 256 + u.val, by omega⟩ := by
  change ∀ r : Fin 8, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (2 : Fin 8))
      (generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (3 : Fin 8))
        (generatedRootEightIncomingTensorStageInteger 2 r))
        (generatedNinthLowerSpinTensorBlockIndex 3 u) =
      2 * generatedRootEightIncomingTensorStageInteger 3 r
        (generatedNinthLowerSpinTensorBlockIndex 3 u)
  simp_rw [generatedRootEight_tensor_fourier_pair_block (2 : Fin 8) 3,
    generatedRootEight_incoming_tensor_stage_block]
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Replay all eight complete source columns using only bounded cached integer coordinates.
private theorem block_04 : ∀ r : Fin 8, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger 2
      (generatedNinthLowerSpinTensorFourierInteger 3
        (generatedRootEightIncomingTensorStageInteger 2 r))
        ⟨4 * 256 + u.val, by omega⟩ =
      2 * generatedRootEightIncomingTensorStageInteger 3 r
        ⟨4 * 256 + u.val, by omega⟩ := by
  change ∀ r : Fin 8, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (2 : Fin 8))
      (generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (3 : Fin 8))
        (generatedRootEightIncomingTensorStageInteger 2 r))
        (generatedNinthLowerSpinTensorBlockIndex 4 u) =
      2 * generatedRootEightIncomingTensorStageInteger 3 r
        (generatedNinthLowerSpinTensorBlockIndex 4 u)
  simp_rw [generatedRootEight_tensor_fourier_pair_block (2 : Fin 8) 3,
    generatedRootEight_incoming_tensor_stage_block]
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Replay all eight complete source columns using only bounded cached integer coordinates.
private theorem block_05 : ∀ r : Fin 8, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger 2
      (generatedNinthLowerSpinTensorFourierInteger 3
        (generatedRootEightIncomingTensorStageInteger 2 r))
        ⟨5 * 256 + u.val, by omega⟩ =
      2 * generatedRootEightIncomingTensorStageInteger 3 r
        ⟨5 * 256 + u.val, by omega⟩ := by
  change ∀ r : Fin 8, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (2 : Fin 8))
      (generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (3 : Fin 8))
        (generatedRootEightIncomingTensorStageInteger 2 r))
        (generatedNinthLowerSpinTensorBlockIndex 5 u) =
      2 * generatedRootEightIncomingTensorStageInteger 3 r
        (generatedNinthLowerSpinTensorBlockIndex 5 u)
  simp_rw [generatedRootEight_tensor_fourier_pair_block (2 : Fin 8) 3,
    generatedRootEight_incoming_tensor_stage_block]
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Replay all eight complete source columns using only bounded cached integer coordinates.
private theorem block_06 : ∀ r : Fin 8, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger 2
      (generatedNinthLowerSpinTensorFourierInteger 3
        (generatedRootEightIncomingTensorStageInteger 2 r))
        ⟨6 * 256 + u.val, by omega⟩ =
      2 * generatedRootEightIncomingTensorStageInteger 3 r
        ⟨6 * 256 + u.val, by omega⟩ := by
  change ∀ r : Fin 8, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (2 : Fin 8))
      (generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (3 : Fin 8))
        (generatedRootEightIncomingTensorStageInteger 2 r))
        (generatedNinthLowerSpinTensorBlockIndex 6 u) =
      2 * generatedRootEightIncomingTensorStageInteger 3 r
        (generatedNinthLowerSpinTensorBlockIndex 6 u)
  simp_rw [generatedRootEight_tensor_fourier_pair_block (2 : Fin 8) 3,
    generatedRootEight_incoming_tensor_stage_block]
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Replay all eight complete source columns using only bounded cached integer coordinates.
private theorem block_07 : ∀ r : Fin 8, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger 2
      (generatedNinthLowerSpinTensorFourierInteger 3
        (generatedRootEightIncomingTensorStageInteger 2 r))
        ⟨7 * 256 + u.val, by omega⟩ =
      2 * generatedRootEightIncomingTensorStageInteger 3 r
        ⟨7 * 256 + u.val, by omega⟩ := by
  change ∀ r : Fin 8, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (2 : Fin 8))
      (generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (3 : Fin 8))
        (generatedRootEightIncomingTensorStageInteger 2 r))
        (generatedNinthLowerSpinTensorBlockIndex 7 u) =
      2 * generatedRootEightIncomingTensorStageInteger 3 r
        (generatedNinthLowerSpinTensorBlockIndex 7 u)
  simp_rw [generatedRootEight_tensor_fourier_pair_block (2 : Fin 8) 3,
    generatedRootEight_incoming_tensor_stage_block]
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Replay all eight complete source columns using only bounded cached integer coordinates.
private theorem block_08 : ∀ r : Fin 8, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger 2
      (generatedNinthLowerSpinTensorFourierInteger 3
        (generatedRootEightIncomingTensorStageInteger 2 r))
        ⟨8 * 256 + u.val, by omega⟩ =
      2 * generatedRootEightIncomingTensorStageInteger 3 r
        ⟨8 * 256 + u.val, by omega⟩ := by
  change ∀ r : Fin 8, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (2 : Fin 8))
      (generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (3 : Fin 8))
        (generatedRootEightIncomingTensorStageInteger 2 r))
        (generatedNinthLowerSpinTensorBlockIndex 8 u) =
      2 * generatedRootEightIncomingTensorStageInteger 3 r
        (generatedNinthLowerSpinTensorBlockIndex 8 u)
  simp_rw [generatedRootEight_tensor_fourier_pair_block (2 : Fin 8) 3,
    generatedRootEight_incoming_tensor_stage_block]
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Replay all eight complete source columns using only bounded cached integer coordinates.
private theorem block_09 : ∀ r : Fin 8, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger 2
      (generatedNinthLowerSpinTensorFourierInteger 3
        (generatedRootEightIncomingTensorStageInteger 2 r))
        ⟨9 * 256 + u.val, by omega⟩ =
      2 * generatedRootEightIncomingTensorStageInteger 3 r
        ⟨9 * 256 + u.val, by omega⟩ := by
  change ∀ r : Fin 8, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (2 : Fin 8))
      (generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (3 : Fin 8))
        (generatedRootEightIncomingTensorStageInteger 2 r))
        (generatedNinthLowerSpinTensorBlockIndex 9 u) =
      2 * generatedRootEightIncomingTensorStageInteger 3 r
        (generatedNinthLowerSpinTensorBlockIndex 9 u)
  simp_rw [generatedRootEight_tensor_fourier_pair_block (2 : Fin 8) 3,
    generatedRootEight_incoming_tensor_stage_block]
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Replay all eight complete source columns using only bounded cached integer coordinates.
private theorem block_10 : ∀ r : Fin 8, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger 2
      (generatedNinthLowerSpinTensorFourierInteger 3
        (generatedRootEightIncomingTensorStageInteger 2 r))
        ⟨10 * 256 + u.val, by omega⟩ =
      2 * generatedRootEightIncomingTensorStageInteger 3 r
        ⟨10 * 256 + u.val, by omega⟩ := by
  change ∀ r : Fin 8, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (2 : Fin 8))
      (generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (3 : Fin 8))
        (generatedRootEightIncomingTensorStageInteger 2 r))
        (generatedNinthLowerSpinTensorBlockIndex 10 u) =
      2 * generatedRootEightIncomingTensorStageInteger 3 r
        (generatedNinthLowerSpinTensorBlockIndex 10 u)
  simp_rw [generatedRootEight_tensor_fourier_pair_block (2 : Fin 8) 3,
    generatedRootEight_incoming_tensor_stage_block]
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Replay all eight complete source columns using only bounded cached integer coordinates.
private theorem block_11 : ∀ r : Fin 8, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger 2
      (generatedNinthLowerSpinTensorFourierInteger 3
        (generatedRootEightIncomingTensorStageInteger 2 r))
        ⟨11 * 256 + u.val, by omega⟩ =
      2 * generatedRootEightIncomingTensorStageInteger 3 r
        ⟨11 * 256 + u.val, by omega⟩ := by
  change ∀ r : Fin 8, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (2 : Fin 8))
      (generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (3 : Fin 8))
        (generatedRootEightIncomingTensorStageInteger 2 r))
        (generatedNinthLowerSpinTensorBlockIndex 11 u) =
      2 * generatedRootEightIncomingTensorStageInteger 3 r
        (generatedNinthLowerSpinTensorBlockIndex 11 u)
  simp_rw [generatedRootEight_tensor_fourier_pair_block (2 : Fin 8) 3,
    generatedRootEight_incoming_tensor_stage_block]
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Replay all eight complete source columns using only bounded cached integer coordinates.
private theorem block_12 : ∀ r : Fin 8, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger 2
      (generatedNinthLowerSpinTensorFourierInteger 3
        (generatedRootEightIncomingTensorStageInteger 2 r))
        ⟨12 * 256 + u.val, by omega⟩ =
      2 * generatedRootEightIncomingTensorStageInteger 3 r
        ⟨12 * 256 + u.val, by omega⟩ := by
  change ∀ r : Fin 8, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (2 : Fin 8))
      (generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (3 : Fin 8))
        (generatedRootEightIncomingTensorStageInteger 2 r))
        (generatedNinthLowerSpinTensorBlockIndex 12 u) =
      2 * generatedRootEightIncomingTensorStageInteger 3 r
        (generatedNinthLowerSpinTensorBlockIndex 12 u)
  simp_rw [generatedRootEight_tensor_fourier_pair_block (2 : Fin 8) 3,
    generatedRootEight_incoming_tensor_stage_block]
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Replay all eight complete source columns using only bounded cached integer coordinates.
private theorem block_13 : ∀ r : Fin 8, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger 2
      (generatedNinthLowerSpinTensorFourierInteger 3
        (generatedRootEightIncomingTensorStageInteger 2 r))
        ⟨13 * 256 + u.val, by omega⟩ =
      2 * generatedRootEightIncomingTensorStageInteger 3 r
        ⟨13 * 256 + u.val, by omega⟩ := by
  change ∀ r : Fin 8, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (2 : Fin 8))
      (generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (3 : Fin 8))
        (generatedRootEightIncomingTensorStageInteger 2 r))
        (generatedNinthLowerSpinTensorBlockIndex 13 u) =
      2 * generatedRootEightIncomingTensorStageInteger 3 r
        (generatedNinthLowerSpinTensorBlockIndex 13 u)
  simp_rw [generatedRootEight_tensor_fourier_pair_block (2 : Fin 8) 3,
    generatedRootEight_incoming_tensor_stage_block]
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Replay all eight complete source columns using only bounded cached integer coordinates.
private theorem block_14 : ∀ r : Fin 8, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger 2
      (generatedNinthLowerSpinTensorFourierInteger 3
        (generatedRootEightIncomingTensorStageInteger 2 r))
        ⟨14 * 256 + u.val, by omega⟩ =
      2 * generatedRootEightIncomingTensorStageInteger 3 r
        ⟨14 * 256 + u.val, by omega⟩ := by
  change ∀ r : Fin 8, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (2 : Fin 8))
      (generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (3 : Fin 8))
        (generatedRootEightIncomingTensorStageInteger 2 r))
        (generatedNinthLowerSpinTensorBlockIndex 14 u) =
      2 * generatedRootEightIncomingTensorStageInteger 3 r
        (generatedNinthLowerSpinTensorBlockIndex 14 u)
  simp_rw [generatedRootEight_tensor_fourier_pair_block (2 : Fin 8) 3,
    generatedRootEight_incoming_tensor_stage_block]
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Replay all eight complete source columns using only bounded cached integer coordinates.
private theorem block_15 : ∀ r : Fin 8, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger 2
      (generatedNinthLowerSpinTensorFourierInteger 3
        (generatedRootEightIncomingTensorStageInteger 2 r))
        ⟨15 * 256 + u.val, by omega⟩ =
      2 * generatedRootEightIncomingTensorStageInteger 3 r
        ⟨15 * 256 + u.val, by omega⟩ := by
  change ∀ r : Fin 8, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (2 : Fin 8))
      (generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 (3 : Fin 8))
        (generatedRootEightIncomingTensorStageInteger 2 r))
        (generatedNinthLowerSpinTensorBlockIndex 15 u) =
      2 * generatedRootEightIncomingTensorStageInteger 3 r
        (generatedNinthLowerSpinTensorBlockIndex 15 u)
  simp_rw [generatedRootEight_tensor_fourier_pair_block (2 : Fin 8) 3,
    generatedRootEight_incoming_tensor_stage_block]
  decide +kernel

/-- Every complete bounded block has its original full coordinate certificate. -/
theorem generatedRootEight_incoming_tensor_pair_02_blocks : ∀ b : Fin 16, ∀ r : Fin 8, ∀ u : Fin 256,
    generatedNinthLowerSpinTensorFourierInteger 2
      (generatedNinthLowerSpinTensorFourierInteger 3
        (generatedRootEightIncomingTensorStageInteger 2 r))
        ⟨b.val * 256 + u.val, by omega⟩ =
      2 * generatedRootEightIncomingTensorStageInteger 3 r
        ⟨b.val * 256 + u.val, by omega⟩ := by
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
