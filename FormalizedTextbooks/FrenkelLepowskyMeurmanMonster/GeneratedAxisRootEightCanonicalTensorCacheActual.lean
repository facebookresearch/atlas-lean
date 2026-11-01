/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalTensorCachePacket00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalTensorCachePacket01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalTensorCachePacket02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalTensorCachePacket03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalTensorCachePacket04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalTensorCachePacket05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalTensorCachePacket06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalTensorCachePacket07

/-! Every original full canonical coefficient sum equals the complete packed integer cache. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- The entire canonical tensor integer cache equals every complete original coefficient sum. -/
theorem generatedRootEight_canonical_tensor_cache_actual (n : Fin 4096) (i : Fin 24) :
    generatedRootEightCanonicalPositiveTensorNumerator n i =
      generatedRootEightCanonicalTensorCache n i := by
  have hq : n.val / 512 < 8 := by omega
  interval_cases h : n.val / 512
  · let m : Fin 512 := ⟨n.val - 0, by omega⟩
    have he : (⟨0 + m.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := generatedRootEight_canonical_tensor_cache_packet_00 m i
    rw [he] at hb
    exact hb
  · let m : Fin 512 := ⟨n.val - 512, by omega⟩
    have he : (⟨512 + m.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := generatedRootEight_canonical_tensor_cache_packet_01 m i
    rw [he] at hb
    exact hb
  · let m : Fin 512 := ⟨n.val - 1024, by omega⟩
    have he : (⟨1024 + m.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := generatedRootEight_canonical_tensor_cache_packet_02 m i
    rw [he] at hb
    exact hb
  · let m : Fin 512 := ⟨n.val - 1536, by omega⟩
    have he : (⟨1536 + m.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := generatedRootEight_canonical_tensor_cache_packet_03 m i
    rw [he] at hb
    exact hb
  · let m : Fin 512 := ⟨n.val - 2048, by omega⟩
    have he : (⟨2048 + m.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := generatedRootEight_canonical_tensor_cache_packet_04 m i
    rw [he] at hb
    exact hb
  · let m : Fin 512 := ⟨n.val - 2560, by omega⟩
    have he : (⟨2560 + m.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := generatedRootEight_canonical_tensor_cache_packet_05 m i
    rw [he] at hb
    exact hb
  · let m : Fin 512 := ⟨n.val - 3072, by omega⟩
    have he : (⟨3072 + m.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := generatedRootEight_canonical_tensor_cache_packet_06 m i
    rw [he] at hb
    exact hb
  · let m : Fin 512 := ⟨n.val - 3584, by omega⟩
    have he : (⟨3584 + m.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := generatedRootEight_canonical_tensor_cache_packet_07 m i
    rw [he] at hb
    exact hb

/-- A genuine actual integer tensor binding transfers to the exact full packed cache. -/
theorem generatedRootEight_canonical_tensor_cache_of_integer_binding
    (h : ∀ t : SpinIndex, ∀ i : Fin 24,
      (griessConwayEncode generatedRootEightCanonicalPositiveAxis).2.2 t i =
        (generatedRootEightCanonicalPositiveTensorNumerator (nortonUIntegerLabel t) i : ℝ) /
          (8192 * Real.sqrt 2)) (t : SpinIndex) (i : Fin 24) :
    (griessConwayEncode generatedRootEightCanonicalPositiveAxis).2.2 t i =
      (generatedRootEightCanonicalTensorCache (nortonUIntegerLabel t) i : ℝ) /
        (8192 * Real.sqrt 2) := by
  rw [h, generatedRootEight_canonical_tensor_cache_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
