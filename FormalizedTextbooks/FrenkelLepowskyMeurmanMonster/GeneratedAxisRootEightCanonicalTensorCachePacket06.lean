/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalTensorCacheData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalTensorSparseSum

/-! Every complete original canonical tensor sum is checked in this bounded label packet. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

set_option maxHeartbeats 16000000 in
-- Compare full original twenty-four-column sums, including every zero and original phase.
private theorem block_00 : ∀ n : Fin 64, ∀ i : Fin 24,
    generatedRootEightCanonicalPositiveTensorNumerator ⟨3072 + n.val, by omega⟩ i =
      generatedRootEightCanonicalTensorCache ⟨3072 + n.val, by omega⟩ i := by
  have hc : ∀ n : Fin 64, ∀ i : Fin 24,
      generatedRootEightCanonicalTensorSparseNumerator ⟨3072 + n.val, by omega⟩ i =
        generatedRootEightCanonicalTensorCache ⟨3072 + n.val, by omega⟩ i := by
    decide +kernel
  intro n i
  rw [generatedRootEight_canonical_tensor_numerator_sparse]
  exact hc n i

set_option maxHeartbeats 16000000 in
-- Compare full original twenty-four-column sums, including every zero and original phase.
private theorem block_01 : ∀ n : Fin 64, ∀ i : Fin 24,
    generatedRootEightCanonicalPositiveTensorNumerator ⟨3136 + n.val, by omega⟩ i =
      generatedRootEightCanonicalTensorCache ⟨3136 + n.val, by omega⟩ i := by
  have hc : ∀ n : Fin 64, ∀ i : Fin 24,
      generatedRootEightCanonicalTensorSparseNumerator ⟨3136 + n.val, by omega⟩ i =
        generatedRootEightCanonicalTensorCache ⟨3136 + n.val, by omega⟩ i := by
    decide +kernel
  intro n i
  rw [generatedRootEight_canonical_tensor_numerator_sparse]
  exact hc n i

set_option maxHeartbeats 16000000 in
-- Compare full original twenty-four-column sums, including every zero and original phase.
private theorem block_02 : ∀ n : Fin 64, ∀ i : Fin 24,
    generatedRootEightCanonicalPositiveTensorNumerator ⟨3200 + n.val, by omega⟩ i =
      generatedRootEightCanonicalTensorCache ⟨3200 + n.val, by omega⟩ i := by
  have hc : ∀ n : Fin 64, ∀ i : Fin 24,
      generatedRootEightCanonicalTensorSparseNumerator ⟨3200 + n.val, by omega⟩ i =
        generatedRootEightCanonicalTensorCache ⟨3200 + n.val, by omega⟩ i := by
    decide +kernel
  intro n i
  rw [generatedRootEight_canonical_tensor_numerator_sparse]
  exact hc n i

set_option maxHeartbeats 16000000 in
-- Compare full original twenty-four-column sums, including every zero and original phase.
private theorem block_03 : ∀ n : Fin 64, ∀ i : Fin 24,
    generatedRootEightCanonicalPositiveTensorNumerator ⟨3264 + n.val, by omega⟩ i =
      generatedRootEightCanonicalTensorCache ⟨3264 + n.val, by omega⟩ i := by
  have hc : ∀ n : Fin 64, ∀ i : Fin 24,
      generatedRootEightCanonicalTensorSparseNumerator ⟨3264 + n.val, by omega⟩ i =
        generatedRootEightCanonicalTensorCache ⟨3264 + n.val, by omega⟩ i := by
    decide +kernel
  intro n i
  rw [generatedRootEight_canonical_tensor_numerator_sparse]
  exact hc n i

set_option maxHeartbeats 16000000 in
-- Compare full original twenty-four-column sums, including every zero and original phase.
private theorem block_04 : ∀ n : Fin 64, ∀ i : Fin 24,
    generatedRootEightCanonicalPositiveTensorNumerator ⟨3328 + n.val, by omega⟩ i =
      generatedRootEightCanonicalTensorCache ⟨3328 + n.val, by omega⟩ i := by
  have hc : ∀ n : Fin 64, ∀ i : Fin 24,
      generatedRootEightCanonicalTensorSparseNumerator ⟨3328 + n.val, by omega⟩ i =
        generatedRootEightCanonicalTensorCache ⟨3328 + n.val, by omega⟩ i := by
    decide +kernel
  intro n i
  rw [generatedRootEight_canonical_tensor_numerator_sparse]
  exact hc n i

set_option maxHeartbeats 16000000 in
-- Compare full original twenty-four-column sums, including every zero and original phase.
private theorem block_05 : ∀ n : Fin 64, ∀ i : Fin 24,
    generatedRootEightCanonicalPositiveTensorNumerator ⟨3392 + n.val, by omega⟩ i =
      generatedRootEightCanonicalTensorCache ⟨3392 + n.val, by omega⟩ i := by
  have hc : ∀ n : Fin 64, ∀ i : Fin 24,
      generatedRootEightCanonicalTensorSparseNumerator ⟨3392 + n.val, by omega⟩ i =
        generatedRootEightCanonicalTensorCache ⟨3392 + n.val, by omega⟩ i := by
    decide +kernel
  intro n i
  rw [generatedRootEight_canonical_tensor_numerator_sparse]
  exact hc n i

set_option maxHeartbeats 16000000 in
-- Compare full original twenty-four-column sums, including every zero and original phase.
private theorem block_06 : ∀ n : Fin 64, ∀ i : Fin 24,
    generatedRootEightCanonicalPositiveTensorNumerator ⟨3456 + n.val, by omega⟩ i =
      generatedRootEightCanonicalTensorCache ⟨3456 + n.val, by omega⟩ i := by
  have hc : ∀ n : Fin 64, ∀ i : Fin 24,
      generatedRootEightCanonicalTensorSparseNumerator ⟨3456 + n.val, by omega⟩ i =
        generatedRootEightCanonicalTensorCache ⟨3456 + n.val, by omega⟩ i := by
    decide +kernel
  intro n i
  rw [generatedRootEight_canonical_tensor_numerator_sparse]
  exact hc n i

set_option maxHeartbeats 16000000 in
-- Compare full original twenty-four-column sums, including every zero and original phase.
private theorem block_07 : ∀ n : Fin 64, ∀ i : Fin 24,
    generatedRootEightCanonicalPositiveTensorNumerator ⟨3520 + n.val, by omega⟩ i =
      generatedRootEightCanonicalTensorCache ⟨3520 + n.val, by omega⟩ i := by
  have hc : ∀ n : Fin 64, ∀ i : Fin 24,
      generatedRootEightCanonicalTensorSparseNumerator ⟨3520 + n.val, by omega⟩ i =
        generatedRootEightCanonicalTensorCache ⟨3520 + n.val, by omega⟩ i := by
    decide +kernel
  intro n i
  rw [generatedRootEight_canonical_tensor_numerator_sparse]
  exact hc n i

/-- Every physical coordinate in this complete canonical label packet equals its original sum. -/
theorem generatedRootEight_canonical_tensor_cache_packet_06 (n : Fin 512) (i : Fin 24) :
    generatedRootEightCanonicalPositiveTensorNumerator ⟨3072 + n.val, by omega⟩ i =
      generatedRootEightCanonicalTensorCache ⟨3072 + n.val, by omega⟩ i := by
  have hq : n.val / 64 < 8 := by omega
  interval_cases h : n.val / 64
  · let m : Fin 64 := ⟨n.val - 0, by omega⟩
    have he : (⟨3072 + m.val, by omega⟩ : Fin 4096) = ⟨3072 + n.val, by omega⟩ := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := block_00 m i
    rw [he] at hb
    exact hb
  · let m : Fin 64 := ⟨n.val - 64, by omega⟩
    have he : (⟨3136 + m.val, by omega⟩ : Fin 4096) = ⟨3072 + n.val, by omega⟩ := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := block_01 m i
    rw [he] at hb
    exact hb
  · let m : Fin 64 := ⟨n.val - 128, by omega⟩
    have he : (⟨3200 + m.val, by omega⟩ : Fin 4096) = ⟨3072 + n.val, by omega⟩ := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := block_02 m i
    rw [he] at hb
    exact hb
  · let m : Fin 64 := ⟨n.val - 192, by omega⟩
    have he : (⟨3264 + m.val, by omega⟩ : Fin 4096) = ⟨3072 + n.val, by omega⟩ := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := block_03 m i
    rw [he] at hb
    exact hb
  · let m : Fin 64 := ⟨n.val - 256, by omega⟩
    have he : (⟨3328 + m.val, by omega⟩ : Fin 4096) = ⟨3072 + n.val, by omega⟩ := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := block_04 m i
    rw [he] at hb
    exact hb
  · let m : Fin 64 := ⟨n.val - 320, by omega⟩
    have he : (⟨3392 + m.val, by omega⟩ : Fin 4096) = ⟨3072 + n.val, by omega⟩ := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := block_05 m i
    rw [he] at hb
    exact hb
  · let m : Fin 64 := ⟨n.val - 384, by omega⟩
    have he : (⟨3456 + m.val, by omega⟩ : Fin 4096) = ⟨3072 + n.val, by omega⟩ := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := block_06 m i
    rw [he] at hb
    exact hb
  · let m : Fin 64 := ⟨n.val - 448, by omega⟩
    have he : (⟨3520 + m.val, by omega⟩ : Fin 4096) = ⟨3072 + n.val, by omega⟩ := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := block_07 m i
    rw [he] at hb
    exact hb

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
