/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverTensorCircuitData

/-! Full actual monomial tensor boundary, including all original signs and zero slots. -/
@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

set_option maxHeartbeats 64000000 in
private theorem boundary_block_00 : ∀ j : Fin 4, ∀ n : Fin 256,
    generatedRootEightMoverTensorSpinInteger 0 ⟨0 + j.val, by omega⟩ ⟨0 + n.val, by omega⟩ =
      8 * generatedRootEightMoverTensorPreInteger
        (fun m => generatedRootEightMoverTensorSourceInteger m ⟨0 + j.val, by omega⟩) ⟨0 + n.val, by omega⟩ := by
  unfold generatedRootEightMoverTensorSpinInteger generatedRootEightMoverTensorPreInteger
    generatedRootEightMoverTensorPreLabel generatedRootEightMoverTensorPreSign
    generatedRootEightMoverTensorSourceInteger generatedRootEightPackedWideBiasedDigit
  decide +kernel

set_option maxHeartbeats 64000000 in
private theorem boundary_block_01 : ∀ j : Fin 4, ∀ n : Fin 256,
    generatedRootEightMoverTensorSpinInteger 0 ⟨0 + j.val, by omega⟩ ⟨256 + n.val, by omega⟩ =
      8 * generatedRootEightMoverTensorPreInteger
        (fun m => generatedRootEightMoverTensorSourceInteger m ⟨0 + j.val, by omega⟩) ⟨256 + n.val, by omega⟩ := by
  unfold generatedRootEightMoverTensorSpinInteger generatedRootEightMoverTensorPreInteger
    generatedRootEightMoverTensorPreLabel generatedRootEightMoverTensorPreSign
    generatedRootEightMoverTensorSourceInteger generatedRootEightPackedWideBiasedDigit
  decide +kernel

set_option maxHeartbeats 64000000 in
private theorem boundary_block_02 : ∀ j : Fin 4, ∀ n : Fin 256,
    generatedRootEightMoverTensorSpinInteger 0 ⟨0 + j.val, by omega⟩ ⟨512 + n.val, by omega⟩ =
      8 * generatedRootEightMoverTensorPreInteger
        (fun m => generatedRootEightMoverTensorSourceInteger m ⟨0 + j.val, by omega⟩) ⟨512 + n.val, by omega⟩ := by
  unfold generatedRootEightMoverTensorSpinInteger generatedRootEightMoverTensorPreInteger
    generatedRootEightMoverTensorPreLabel generatedRootEightMoverTensorPreSign
    generatedRootEightMoverTensorSourceInteger generatedRootEightPackedWideBiasedDigit
  decide +kernel

set_option maxHeartbeats 64000000 in
private theorem boundary_block_03 : ∀ j : Fin 4, ∀ n : Fin 256,
    generatedRootEightMoverTensorSpinInteger 0 ⟨0 + j.val, by omega⟩ ⟨768 + n.val, by omega⟩ =
      8 * generatedRootEightMoverTensorPreInteger
        (fun m => generatedRootEightMoverTensorSourceInteger m ⟨0 + j.val, by omega⟩) ⟨768 + n.val, by omega⟩ := by
  unfold generatedRootEightMoverTensorSpinInteger generatedRootEightMoverTensorPreInteger
    generatedRootEightMoverTensorPreLabel generatedRootEightMoverTensorPreSign
    generatedRootEightMoverTensorSourceInteger generatedRootEightPackedWideBiasedDigit
  decide +kernel

set_option maxHeartbeats 64000000 in
private theorem boundary_block_04 : ∀ j : Fin 4, ∀ n : Fin 256,
    generatedRootEightMoverTensorSpinInteger 0 ⟨0 + j.val, by omega⟩ ⟨1024 + n.val, by omega⟩ =
      8 * generatedRootEightMoverTensorPreInteger
        (fun m => generatedRootEightMoverTensorSourceInteger m ⟨0 + j.val, by omega⟩) ⟨1024 + n.val, by omega⟩ := by
  unfold generatedRootEightMoverTensorSpinInteger generatedRootEightMoverTensorPreInteger
    generatedRootEightMoverTensorPreLabel generatedRootEightMoverTensorPreSign
    generatedRootEightMoverTensorSourceInteger generatedRootEightPackedWideBiasedDigit
  decide +kernel

set_option maxHeartbeats 64000000 in
private theorem boundary_block_05 : ∀ j : Fin 4, ∀ n : Fin 256,
    generatedRootEightMoverTensorSpinInteger 0 ⟨0 + j.val, by omega⟩ ⟨1280 + n.val, by omega⟩ =
      8 * generatedRootEightMoverTensorPreInteger
        (fun m => generatedRootEightMoverTensorSourceInteger m ⟨0 + j.val, by omega⟩) ⟨1280 + n.val, by omega⟩ := by
  unfold generatedRootEightMoverTensorSpinInteger generatedRootEightMoverTensorPreInteger
    generatedRootEightMoverTensorPreLabel generatedRootEightMoverTensorPreSign
    generatedRootEightMoverTensorSourceInteger generatedRootEightPackedWideBiasedDigit
  decide +kernel

set_option maxHeartbeats 64000000 in
private theorem boundary_block_06 : ∀ j : Fin 4, ∀ n : Fin 256,
    generatedRootEightMoverTensorSpinInteger 0 ⟨0 + j.val, by omega⟩ ⟨1536 + n.val, by omega⟩ =
      8 * generatedRootEightMoverTensorPreInteger
        (fun m => generatedRootEightMoverTensorSourceInteger m ⟨0 + j.val, by omega⟩) ⟨1536 + n.val, by omega⟩ := by
  unfold generatedRootEightMoverTensorSpinInteger generatedRootEightMoverTensorPreInteger
    generatedRootEightMoverTensorPreLabel generatedRootEightMoverTensorPreSign
    generatedRootEightMoverTensorSourceInteger generatedRootEightPackedWideBiasedDigit
  decide +kernel

set_option maxHeartbeats 64000000 in
private theorem boundary_block_07 : ∀ j : Fin 4, ∀ n : Fin 256,
    generatedRootEightMoverTensorSpinInteger 0 ⟨0 + j.val, by omega⟩ ⟨1792 + n.val, by omega⟩ =
      8 * generatedRootEightMoverTensorPreInteger
        (fun m => generatedRootEightMoverTensorSourceInteger m ⟨0 + j.val, by omega⟩) ⟨1792 + n.val, by omega⟩ := by
  unfold generatedRootEightMoverTensorSpinInteger generatedRootEightMoverTensorPreInteger
    generatedRootEightMoverTensorPreLabel generatedRootEightMoverTensorPreSign
    generatedRootEightMoverTensorSourceInteger generatedRootEightPackedWideBiasedDigit
  decide +kernel

set_option maxHeartbeats 64000000 in
private theorem boundary_block_08 : ∀ j : Fin 4, ∀ n : Fin 256,
    generatedRootEightMoverTensorSpinInteger 0 ⟨0 + j.val, by omega⟩ ⟨2048 + n.val, by omega⟩ =
      8 * generatedRootEightMoverTensorPreInteger
        (fun m => generatedRootEightMoverTensorSourceInteger m ⟨0 + j.val, by omega⟩) ⟨2048 + n.val, by omega⟩ := by
  unfold generatedRootEightMoverTensorSpinInteger generatedRootEightMoverTensorPreInteger
    generatedRootEightMoverTensorPreLabel generatedRootEightMoverTensorPreSign
    generatedRootEightMoverTensorSourceInteger generatedRootEightPackedWideBiasedDigit
  decide +kernel

set_option maxHeartbeats 64000000 in
private theorem boundary_block_09 : ∀ j : Fin 4, ∀ n : Fin 256,
    generatedRootEightMoverTensorSpinInteger 0 ⟨0 + j.val, by omega⟩ ⟨2304 + n.val, by omega⟩ =
      8 * generatedRootEightMoverTensorPreInteger
        (fun m => generatedRootEightMoverTensorSourceInteger m ⟨0 + j.val, by omega⟩) ⟨2304 + n.val, by omega⟩ := by
  unfold generatedRootEightMoverTensorSpinInteger generatedRootEightMoverTensorPreInteger
    generatedRootEightMoverTensorPreLabel generatedRootEightMoverTensorPreSign
    generatedRootEightMoverTensorSourceInteger generatedRootEightPackedWideBiasedDigit
  decide +kernel

set_option maxHeartbeats 64000000 in
private theorem boundary_block_10 : ∀ j : Fin 4, ∀ n : Fin 256,
    generatedRootEightMoverTensorSpinInteger 0 ⟨0 + j.val, by omega⟩ ⟨2560 + n.val, by omega⟩ =
      8 * generatedRootEightMoverTensorPreInteger
        (fun m => generatedRootEightMoverTensorSourceInteger m ⟨0 + j.val, by omega⟩) ⟨2560 + n.val, by omega⟩ := by
  unfold generatedRootEightMoverTensorSpinInteger generatedRootEightMoverTensorPreInteger
    generatedRootEightMoverTensorPreLabel generatedRootEightMoverTensorPreSign
    generatedRootEightMoverTensorSourceInteger generatedRootEightPackedWideBiasedDigit
  decide +kernel

set_option maxHeartbeats 64000000 in
private theorem boundary_block_11 : ∀ j : Fin 4, ∀ n : Fin 256,
    generatedRootEightMoverTensorSpinInteger 0 ⟨0 + j.val, by omega⟩ ⟨2816 + n.val, by omega⟩ =
      8 * generatedRootEightMoverTensorPreInteger
        (fun m => generatedRootEightMoverTensorSourceInteger m ⟨0 + j.val, by omega⟩) ⟨2816 + n.val, by omega⟩ := by
  unfold generatedRootEightMoverTensorSpinInteger generatedRootEightMoverTensorPreInteger
    generatedRootEightMoverTensorPreLabel generatedRootEightMoverTensorPreSign
    generatedRootEightMoverTensorSourceInteger generatedRootEightPackedWideBiasedDigit
  decide +kernel

set_option maxHeartbeats 64000000 in
private theorem boundary_block_12 : ∀ j : Fin 4, ∀ n : Fin 256,
    generatedRootEightMoverTensorSpinInteger 0 ⟨0 + j.val, by omega⟩ ⟨3072 + n.val, by omega⟩ =
      8 * generatedRootEightMoverTensorPreInteger
        (fun m => generatedRootEightMoverTensorSourceInteger m ⟨0 + j.val, by omega⟩) ⟨3072 + n.val, by omega⟩ := by
  unfold generatedRootEightMoverTensorSpinInteger generatedRootEightMoverTensorPreInteger
    generatedRootEightMoverTensorPreLabel generatedRootEightMoverTensorPreSign
    generatedRootEightMoverTensorSourceInteger generatedRootEightPackedWideBiasedDigit
  decide +kernel

set_option maxHeartbeats 64000000 in
private theorem boundary_block_13 : ∀ j : Fin 4, ∀ n : Fin 256,
    generatedRootEightMoverTensorSpinInteger 0 ⟨0 + j.val, by omega⟩ ⟨3328 + n.val, by omega⟩ =
      8 * generatedRootEightMoverTensorPreInteger
        (fun m => generatedRootEightMoverTensorSourceInteger m ⟨0 + j.val, by omega⟩) ⟨3328 + n.val, by omega⟩ := by
  unfold generatedRootEightMoverTensorSpinInteger generatedRootEightMoverTensorPreInteger
    generatedRootEightMoverTensorPreLabel generatedRootEightMoverTensorPreSign
    generatedRootEightMoverTensorSourceInteger generatedRootEightPackedWideBiasedDigit
  decide +kernel

set_option maxHeartbeats 64000000 in
private theorem boundary_block_14 : ∀ j : Fin 4, ∀ n : Fin 256,
    generatedRootEightMoverTensorSpinInteger 0 ⟨0 + j.val, by omega⟩ ⟨3584 + n.val, by omega⟩ =
      8 * generatedRootEightMoverTensorPreInteger
        (fun m => generatedRootEightMoverTensorSourceInteger m ⟨0 + j.val, by omega⟩) ⟨3584 + n.val, by omega⟩ := by
  unfold generatedRootEightMoverTensorSpinInteger generatedRootEightMoverTensorPreInteger
    generatedRootEightMoverTensorPreLabel generatedRootEightMoverTensorPreSign
    generatedRootEightMoverTensorSourceInteger generatedRootEightPackedWideBiasedDigit
  decide +kernel

set_option maxHeartbeats 64000000 in
private theorem boundary_block_15 : ∀ j : Fin 4, ∀ n : Fin 256,
    generatedRootEightMoverTensorSpinInteger 0 ⟨0 + j.val, by omega⟩ ⟨3840 + n.val, by omega⟩ =
      8 * generatedRootEightMoverTensorPreInteger
        (fun m => generatedRootEightMoverTensorSourceInteger m ⟨0 + j.val, by omega⟩) ⟨3840 + n.val, by omega⟩ := by
  unfold generatedRootEightMoverTensorSpinInteger generatedRootEightMoverTensorPreInteger
    generatedRootEightMoverTensorPreLabel generatedRootEightMoverTensorPreSign
    generatedRootEightMoverTensorSourceInteger generatedRootEightPackedWideBiasedDigit
  decide +kernel

private theorem boundary_by_block (b : Fin 16) (j : Fin 4) (n : Fin 4096)
    (hb : n.val / 256 = b.val) :
    generatedRootEightMoverTensorSpinInteger 0 ⟨0 + j.val, by omega⟩ n =
      8 * generatedRootEightMoverTensorPreInteger
        (fun m => generatedRootEightMoverTensorSourceInteger m ⟨0 + j.val, by omega⟩) n := by
  fin_cases b
  · change n.val / 256 = 0 at hb
    let u : Fin 256 := ⟨n.val % 256, Nat.mod_lt _ (by decide)⟩
    have hn : (⟨0 + u.val, by dsimp only [u]; omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [u]
      omega
    simpa only [hn] using boundary_block_00 j u
  · change n.val / 256 = 1 at hb
    let u : Fin 256 := ⟨n.val % 256, Nat.mod_lt _ (by decide)⟩
    have hn : (⟨256 + u.val, by dsimp only [u]; omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [u]
      omega
    simpa only [hn] using boundary_block_01 j u
  · change n.val / 256 = 2 at hb
    let u : Fin 256 := ⟨n.val % 256, Nat.mod_lt _ (by decide)⟩
    have hn : (⟨512 + u.val, by dsimp only [u]; omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [u]
      omega
    simpa only [hn] using boundary_block_02 j u
  · change n.val / 256 = 3 at hb
    let u : Fin 256 := ⟨n.val % 256, Nat.mod_lt _ (by decide)⟩
    have hn : (⟨768 + u.val, by dsimp only [u]; omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [u]
      omega
    simpa only [hn] using boundary_block_03 j u
  · change n.val / 256 = 4 at hb
    let u : Fin 256 := ⟨n.val % 256, Nat.mod_lt _ (by decide)⟩
    have hn : (⟨1024 + u.val, by dsimp only [u]; omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [u]
      omega
    simpa only [hn] using boundary_block_04 j u
  · change n.val / 256 = 5 at hb
    let u : Fin 256 := ⟨n.val % 256, Nat.mod_lt _ (by decide)⟩
    have hn : (⟨1280 + u.val, by dsimp only [u]; omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [u]
      omega
    simpa only [hn] using boundary_block_05 j u
  · change n.val / 256 = 6 at hb
    let u : Fin 256 := ⟨n.val % 256, Nat.mod_lt _ (by decide)⟩
    have hn : (⟨1536 + u.val, by dsimp only [u]; omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [u]
      omega
    simpa only [hn] using boundary_block_06 j u
  · change n.val / 256 = 7 at hb
    let u : Fin 256 := ⟨n.val % 256, Nat.mod_lt _ (by decide)⟩
    have hn : (⟨1792 + u.val, by dsimp only [u]; omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [u]
      omega
    simpa only [hn] using boundary_block_07 j u
  · change n.val / 256 = 8 at hb
    let u : Fin 256 := ⟨n.val % 256, Nat.mod_lt _ (by decide)⟩
    have hn : (⟨2048 + u.val, by dsimp only [u]; omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [u]
      omega
    simpa only [hn] using boundary_block_08 j u
  · change n.val / 256 = 9 at hb
    let u : Fin 256 := ⟨n.val % 256, Nat.mod_lt _ (by decide)⟩
    have hn : (⟨2304 + u.val, by dsimp only [u]; omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [u]
      omega
    simpa only [hn] using boundary_block_09 j u
  · change n.val / 256 = 10 at hb
    let u : Fin 256 := ⟨n.val % 256, Nat.mod_lt _ (by decide)⟩
    have hn : (⟨2560 + u.val, by dsimp only [u]; omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [u]
      omega
    simpa only [hn] using boundary_block_10 j u
  · change n.val / 256 = 11 at hb
    let u : Fin 256 := ⟨n.val % 256, Nat.mod_lt _ (by decide)⟩
    have hn : (⟨2816 + u.val, by dsimp only [u]; omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [u]
      omega
    simpa only [hn] using boundary_block_11 j u
  · change n.val / 256 = 12 at hb
    let u : Fin 256 := ⟨n.val % 256, Nat.mod_lt _ (by decide)⟩
    have hn : (⟨3072 + u.val, by dsimp only [u]; omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [u]
      omega
    simpa only [hn] using boundary_block_12 j u
  · change n.val / 256 = 13 at hb
    let u : Fin 256 := ⟨n.val % 256, Nat.mod_lt _ (by decide)⟩
    have hn : (⟨3328 + u.val, by dsimp only [u]; omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [u]
      omega
    simpa only [hn] using boundary_block_13 j u
  · change n.val / 256 = 14 at hb
    let u : Fin 256 := ⟨n.val % 256, Nat.mod_lt _ (by decide)⟩
    have hn : (⟨3584 + u.val, by dsimp only [u]; omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [u]
      omega
    simpa only [hn] using boundary_block_14 j u
  · change n.val / 256 = 15 at hb
    let u : Fin 256 := ⟨n.val % 256, Nat.mod_lt _ (by decide)⟩
    have hn : (⟨3840 + u.val, by dsimp only [u]; omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [u]
      omega
    simpa only [hn] using boundary_block_15 j u

/-- This complete original boundary holds on all four physical rows. -/
theorem generatedRootEight_mover_tensor_start_packet_00
    (j : Fin 4) (n : Fin 4096) :
    generatedRootEightMoverTensorSpinInteger 0 ⟨0 + j.val, by omega⟩ n =
      8 * generatedRootEightMoverTensorPreInteger
        (fun m => generatedRootEightMoverTensorSourceInteger m ⟨0 + j.val, by omega⟩) n :=
  boundary_by_block ⟨n.val / 256, by omega⟩ j n rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
