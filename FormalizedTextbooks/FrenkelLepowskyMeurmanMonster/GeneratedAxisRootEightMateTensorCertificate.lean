/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMateTensorPacket00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMateTensorPacket01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMateTensorPacket02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMateTensorPacket03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMateTensorPacket04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMateTensorPacket05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMateTensorPacket06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMateTensorPacket07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMateTensorPacket08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMateTensorPacket09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMateTensorPacket10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMateTensorPacket11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMateTensorPacket12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMateTensorPacket13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMateTensorPacket14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMateTensorPacket15

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMateTensorAddressCertificate

/-! Whole original actual mate tensor fixation. -/
@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Every original tensor coordinate satisfies the complete actual integer equation. -/
theorem generatedRootEight_mate_tensor_cache_actual (n : Fin 4096) (i : Fin 24) :
    generatedRootEightMateTensorCacheCondition n i := by
  have hq : n.val / 256 < 16 := by omega
  interval_cases h : n.val / 256
  · let u : Fin 256 := ⟨n.val - 0, by omega⟩
    have he : (⟨0 * 256 + u.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [u]
      omega
    have hb := generatedRootEight_mate_tensor_cache_block_00 u i
    rw [he] at hb
    exact hb
  · let u : Fin 256 := ⟨n.val - 256, by omega⟩
    have he : (⟨1 * 256 + u.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [u]
      omega
    have hb := generatedRootEight_mate_tensor_cache_block_01 u i
    rw [he] at hb
    exact hb
  · let u : Fin 256 := ⟨n.val - 512, by omega⟩
    have he : (⟨2 * 256 + u.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [u]
      omega
    have hb := generatedRootEight_mate_tensor_cache_block_02 u i
    rw [he] at hb
    exact hb
  · let u : Fin 256 := ⟨n.val - 768, by omega⟩
    have he : (⟨3 * 256 + u.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [u]
      omega
    have hb := generatedRootEight_mate_tensor_cache_block_03 u i
    rw [he] at hb
    exact hb
  · let u : Fin 256 := ⟨n.val - 1024, by omega⟩
    have he : (⟨4 * 256 + u.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [u]
      omega
    have hb := generatedRootEight_mate_tensor_cache_block_04 u i
    rw [he] at hb
    exact hb
  · let u : Fin 256 := ⟨n.val - 1280, by omega⟩
    have he : (⟨5 * 256 + u.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [u]
      omega
    have hb := generatedRootEight_mate_tensor_cache_block_05 u i
    rw [he] at hb
    exact hb
  · let u : Fin 256 := ⟨n.val - 1536, by omega⟩
    have he : (⟨6 * 256 + u.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [u]
      omega
    have hb := generatedRootEight_mate_tensor_cache_block_06 u i
    rw [he] at hb
    exact hb
  · let u : Fin 256 := ⟨n.val - 1792, by omega⟩
    have he : (⟨7 * 256 + u.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [u]
      omega
    have hb := generatedRootEight_mate_tensor_cache_block_07 u i
    rw [he] at hb
    exact hb
  · let u : Fin 256 := ⟨n.val - 2048, by omega⟩
    have he : (⟨8 * 256 + u.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [u]
      omega
    have hb := generatedRootEight_mate_tensor_cache_block_08 u i
    rw [he] at hb
    exact hb
  · let u : Fin 256 := ⟨n.val - 2304, by omega⟩
    have he : (⟨9 * 256 + u.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [u]
      omega
    have hb := generatedRootEight_mate_tensor_cache_block_09 u i
    rw [he] at hb
    exact hb
  · let u : Fin 256 := ⟨n.val - 2560, by omega⟩
    have he : (⟨10 * 256 + u.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [u]
      omega
    have hb := generatedRootEight_mate_tensor_cache_block_10 u i
    rw [he] at hb
    exact hb
  · let u : Fin 256 := ⟨n.val - 2816, by omega⟩
    have he : (⟨11 * 256 + u.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [u]
      omega
    have hb := generatedRootEight_mate_tensor_cache_block_11 u i
    rw [he] at hb
    exact hb
  · let u : Fin 256 := ⟨n.val - 3072, by omega⟩
    have he : (⟨12 * 256 + u.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [u]
      omega
    have hb := generatedRootEight_mate_tensor_cache_block_12 u i
    rw [he] at hb
    exact hb
  · let u : Fin 256 := ⟨n.val - 3328, by omega⟩
    have he : (⟨13 * 256 + u.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [u]
      omega
    have hb := generatedRootEight_mate_tensor_cache_block_13 u i
    rw [he] at hb
    exact hb
  · let u : Fin 256 := ⟨n.val - 3584, by omega⟩
    have he : (⟨14 * 256 + u.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [u]
      omega
    have hb := generatedRootEight_mate_tensor_cache_block_14 u i
    rw [he] at hb
    exact hb
  · let u : Fin 256 := ⟨n.val - 3840, by omega⟩
    have he : (⟨15 * 256 + u.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [u]
      omega
    have hb := generatedRootEight_mate_tensor_cache_block_15 u i
    rw [he] at hb
    exact hb

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
