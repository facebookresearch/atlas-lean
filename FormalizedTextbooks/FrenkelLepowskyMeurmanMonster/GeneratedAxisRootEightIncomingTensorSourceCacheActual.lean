/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingTensorSourceCachePacket00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingTensorSourceCachePacket01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingTensorSourceCachePacket02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingTensorSourceCachePacket03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingTensorFactors

/-! Complete source input cache equality, bound to every actual original spin coefficient. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- All 4096 labels of all eight actual source spin columns equal the literal signed cache. -/
theorem generatedRootEight_incoming_tensor_source_cache_actual (r : Fin 8) (k : Fin 4096) :
    generatedTwelfthTensorSourceSpin r k = generatedRootEightIncomingTensorSourceCache r k := by
  rw [generatedTwelfth_tensor_source_spin_small_actual]
  have hc : k.val < 1024 ∨ (1024 ≤ k.val ∧ k.val < 2048) ∨
      (2048 ≤ k.val ∧ k.val < 3072) ∨ 3072 ≤ k.val := by omega
  rcases hc with h | ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩ | h
  · let n : Fin 1024 := ⟨k.val - 0, by omega⟩
    have he : (⟨0 + n.val, by omega⟩ : Fin 4096) = k := by
      apply Fin.ext
      dsimp [n]
      omega
    have ht := generatedRootEight_incoming_tensor_source_cache_packet00 r n
    rw [he] at ht
    exact ht
  · let n : Fin 1024 := ⟨k.val - 1024, by omega⟩
    have he : (⟨1024 + n.val, by omega⟩ : Fin 4096) = k := by
      apply Fin.ext
      dsimp [n]
      omega
    have ht := generatedRootEight_incoming_tensor_source_cache_packet01 r n
    rw [he] at ht
    exact ht
  · let n : Fin 1024 := ⟨k.val - 2048, by omega⟩
    have he : (⟨2048 + n.val, by omega⟩ : Fin 4096) = k := by
      apply Fin.ext
      dsimp [n]
      omega
    have ht := generatedRootEight_incoming_tensor_source_cache_packet02 r n
    rw [he] at ht
    exact ht
  · let n : Fin 1024 := ⟨k.val - 3072, by omega⟩
    have he : (⟨3072 + n.val, by omega⟩ : Fin 4096) = k := by
      apply Fin.ext
      dsimp [n]
      omega
    have ht := generatedRootEight_incoming_tensor_source_cache_packet03 r n
    rw [he] at ht
    exact ht

/-- The cache gives every original real spin coefficient with the genuine square-root factor. -/
theorem generatedRootEight_incoming_tensor_source_spin_cache (r : Fin 8) (t : SpinIndex) :
    generatedRootEightIncomingTensorSourceSpin r t =
      (generatedRootEightIncomingTensorSourceCache r (generatedAxisGlobalSpinLabel t) : ℝ) /
        Real.sqrt 2 := by
  unfold generatedRootEightIncomingTensorSourceSpin
  rw [generatedRootEight_incoming_tensor_source_cache_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
