/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMateTensorPacket12Block00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMateTensorPacket12Block01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMateTensorPacket12Block02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMateTensorPacket12Block03

/-! Complete bounded actual mate tensor packet. -/
@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every original tensor coordinate in this packet is certified. -/
theorem generatedRootEight_mate_tensor_cache_block_12 (u : Fin 256) (i : Fin 24) :
    generatedRootEightMateTensorCacheCondition ⟨12 * 256 + u.val, by omega⟩ i := by
  have hq : u.val / 64 < 4 := by omega
  interval_cases h : u.val / 64
  · let v : Fin 64 := ⟨u.val - 0, by omega⟩
    have he : (⟨3072 + v.val, by omega⟩ : Fin 4096) =
        ⟨12 * 256 + u.val, by omega⟩ := by
      apply Fin.ext
      dsimp only [v]
      omega
    have hb := generatedRootEight_mate_tensor_cache_block_12_00 v i
    rw [he] at hb
    exact hb
  · let v : Fin 64 := ⟨u.val - 64, by omega⟩
    have he : (⟨3136 + v.val, by omega⟩ : Fin 4096) =
        ⟨12 * 256 + u.val, by omega⟩ := by
      apply Fin.ext
      dsimp only [v]
      omega
    have hb := generatedRootEight_mate_tensor_cache_block_12_01 v i
    rw [he] at hb
    exact hb
  · let v : Fin 64 := ⟨u.val - 128, by omega⟩
    have he : (⟨3200 + v.val, by omega⟩ : Fin 4096) =
        ⟨12 * 256 + u.val, by omega⟩ := by
      apply Fin.ext
      dsimp only [v]
      omega
    have hb := generatedRootEight_mate_tensor_cache_block_12_02 v i
    rw [he] at hb
    exact hb
  · let v : Fin 64 := ⟨u.val - 192, by omega⟩
    have he : (⟨3264 + v.val, by omega⟩ : Fin 4096) =
        ⟨12 * 256 + u.val, by omega⟩ := by
      apply Fin.ext
      dsimp only [v]
      omega
    have hb := generatedRootEight_mate_tensor_cache_block_12_03 v i
    rw [he] at hb
    exact hb

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
