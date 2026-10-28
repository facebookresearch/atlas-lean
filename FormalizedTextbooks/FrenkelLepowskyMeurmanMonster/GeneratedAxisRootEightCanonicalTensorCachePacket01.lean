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
    generatedRootEightCanonicalPositiveTensorNumerator ⟨512 + n.val, by omega⟩ i =
      generatedRootEightCanonicalTensorCache ⟨512 + n.val, by omega⟩ i := by
  have hc : ∀ n : Fin 64, ∀ i : Fin 24,
      generatedRootEightCanonicalTensorSparseNumerator ⟨512 + n.val, by omega⟩ i =
        generatedRootEightCanonicalTensorCache ⟨512 + n.val, by omega⟩ i := by
    decide +kernel
  intro n i
  rw [generatedRootEight_canonical_tensor_numerator_sparse]
  exact hc n i

set_option maxHeartbeats 16000000 in
-- Compare full original twenty-four-column sums, including every zero and original phase.
private theorem block_01 : ∀ n : Fin 64, ∀ i : Fin 24,
    generatedRootEightCanonicalPositiveTensorNumerator ⟨576 + n.val, by omega⟩ i =
      generatedRootEightCanonicalTensorCache ⟨576 + n.val, by omega⟩ i := by
  have hc : ∀ n : Fin 64, ∀ i : Fin 24,
      generatedRootEightCanonicalTensorSparseNumerator ⟨576 + n.val, by omega⟩ i =
        generatedRootEightCanonicalTensorCache ⟨576 + n.val, by omega⟩ i := by
    decide +kernel
  intro n i
  rw [generatedRootEight_canonical_tensor_numerator_sparse]
  exact hc n i

set_option maxHeartbeats 16000000 in
-- Compare full original twenty-four-column sums, including every zero and original phase.
private theorem block_02 : ∀ n : Fin 64, ∀ i : Fin 24,
    generatedRootEightCanonicalPositiveTensorNumerator ⟨640 + n.val, by omega⟩ i =
      generatedRootEightCanonicalTensorCache ⟨640 + n.val, by omega⟩ i := by
  have hc : ∀ n : Fin 64, ∀ i : Fin 24,
      generatedRootEightCanonicalTensorSparseNumerator ⟨640 + n.val, by omega⟩ i =
        generatedRootEightCanonicalTensorCache ⟨640 + n.val, by omega⟩ i := by
    decide +kernel
  intro n i
  rw [generatedRootEight_canonical_tensor_numerator_sparse]
  exact hc n i

set_option maxHeartbeats 16000000 in
-- Compare full original twenty-four-column sums, including every zero and original phase.
private theorem block_03 : ∀ n : Fin 64, ∀ i : Fin 24,
    generatedRootEightCanonicalPositiveTensorNumerator ⟨704 + n.val, by omega⟩ i =
      generatedRootEightCanonicalTensorCache ⟨704 + n.val, by omega⟩ i := by
  have hc : ∀ n : Fin 64, ∀ i : Fin 24,
      generatedRootEightCanonicalTensorSparseNumerator ⟨704 + n.val, by omega⟩ i =
        generatedRootEightCanonicalTensorCache ⟨704 + n.val, by omega⟩ i := by
    decide +kernel
  intro n i
  rw [generatedRootEight_canonical_tensor_numerator_sparse]
  exact hc n i

set_option maxHeartbeats 16000000 in
-- Compare full original twenty-four-column sums, including every zero and original phase.
private theorem block_04 : ∀ n : Fin 64, ∀ i : Fin 24,
    generatedRootEightCanonicalPositiveTensorNumerator ⟨768 + n.val, by omega⟩ i =
      generatedRootEightCanonicalTensorCache ⟨768 + n.val, by omega⟩ i := by
  have hc : ∀ n : Fin 64, ∀ i : Fin 24,
      generatedRootEightCanonicalTensorSparseNumerator ⟨768 + n.val, by omega⟩ i =
        generatedRootEightCanonicalTensorCache ⟨768 + n.val, by omega⟩ i := by
    decide +kernel
  intro n i
  rw [generatedRootEight_canonical_tensor_numerator_sparse]
  exact hc n i

set_option maxHeartbeats 16000000 in
-- Compare full original twenty-four-column sums, including every zero and original phase.
private theorem block_05 : ∀ n : Fin 64, ∀ i : Fin 24,
    generatedRootEightCanonicalPositiveTensorNumerator ⟨832 + n.val, by omega⟩ i =
      generatedRootEightCanonicalTensorCache ⟨832 + n.val, by omega⟩ i := by
  have hc : ∀ n : Fin 64, ∀ i : Fin 24,
      generatedRootEightCanonicalTensorSparseNumerator ⟨832 + n.val, by omega⟩ i =
        generatedRootEightCanonicalTensorCache ⟨832 + n.val, by omega⟩ i := by
    decide +kernel
  intro n i
  rw [generatedRootEight_canonical_tensor_numerator_sparse]
  exact hc n i

set_option maxHeartbeats 16000000 in
-- Compare full original twenty-four-column sums, including every zero and original phase.
private theorem block_06 : ∀ n : Fin 64, ∀ i : Fin 24,
    generatedRootEightCanonicalPositiveTensorNumerator ⟨896 + n.val, by omega⟩ i =
      generatedRootEightCanonicalTensorCache ⟨896 + n.val, by omega⟩ i := by
  have hc : ∀ n : Fin 64, ∀ i : Fin 24,
      generatedRootEightCanonicalTensorSparseNumerator ⟨896 + n.val, by omega⟩ i =
        generatedRootEightCanonicalTensorCache ⟨896 + n.val, by omega⟩ i := by
    decide +kernel
  intro n i
  rw [generatedRootEight_canonical_tensor_numerator_sparse]
  exact hc n i

set_option maxHeartbeats 16000000 in
-- Compare full original twenty-four-column sums, including every zero and original phase.
private theorem block_07 : ∀ n : Fin 64, ∀ i : Fin 24,
    generatedRootEightCanonicalPositiveTensorNumerator ⟨960 + n.val, by omega⟩ i =
      generatedRootEightCanonicalTensorCache ⟨960 + n.val, by omega⟩ i := by
  have hc : ∀ n : Fin 64, ∀ i : Fin 24,
      generatedRootEightCanonicalTensorSparseNumerator ⟨960 + n.val, by omega⟩ i =
        generatedRootEightCanonicalTensorCache ⟨960 + n.val, by omega⟩ i := by
    decide +kernel
  intro n i
  rw [generatedRootEight_canonical_tensor_numerator_sparse]
  exact hc n i

/-- Every physical coordinate in this complete canonical label packet equals its original sum. -/
theorem generatedRootEight_canonical_tensor_cache_packet_01 (n : Fin 512) (i : Fin 24) :
    generatedRootEightCanonicalPositiveTensorNumerator ⟨512 + n.val, by omega⟩ i =
      generatedRootEightCanonicalTensorCache ⟨512 + n.val, by omega⟩ i := by
  have hq : n.val / 64 < 8 := by omega
  interval_cases h : n.val / 64
  · let m : Fin 64 := ⟨n.val - 0, by omega⟩
    have he : (⟨512 + m.val, by omega⟩ : Fin 4096) = ⟨512 + n.val, by omega⟩ := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := block_00 m i
    rw [he] at hb
    exact hb
  · let m : Fin 64 := ⟨n.val - 64, by omega⟩
    have he : (⟨576 + m.val, by omega⟩ : Fin 4096) = ⟨512 + n.val, by omega⟩ := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := block_01 m i
    rw [he] at hb
    exact hb
  · let m : Fin 64 := ⟨n.val - 128, by omega⟩
    have he : (⟨640 + m.val, by omega⟩ : Fin 4096) = ⟨512 + n.val, by omega⟩ := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := block_02 m i
    rw [he] at hb
    exact hb
  · let m : Fin 64 := ⟨n.val - 192, by omega⟩
    have he : (⟨704 + m.val, by omega⟩ : Fin 4096) = ⟨512 + n.val, by omega⟩ := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := block_03 m i
    rw [he] at hb
    exact hb
  · let m : Fin 64 := ⟨n.val - 256, by omega⟩
    have he : (⟨768 + m.val, by omega⟩ : Fin 4096) = ⟨512 + n.val, by omega⟩ := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := block_04 m i
    rw [he] at hb
    exact hb
  · let m : Fin 64 := ⟨n.val - 320, by omega⟩
    have he : (⟨832 + m.val, by omega⟩ : Fin 4096) = ⟨512 + n.val, by omega⟩ := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := block_05 m i
    rw [he] at hb
    exact hb
  · let m : Fin 64 := ⟨n.val - 384, by omega⟩
    have he : (⟨896 + m.val, by omega⟩ : Fin 4096) = ⟨512 + n.val, by omega⟩ := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := block_06 m i
    rw [he] at hb
    exact hb
  · let m : Fin 64 := ⟨n.val - 448, by omega⟩
    have he : (⟨960 + m.val, by omega⟩ : Fin 4096) = ⟨512 + n.val, by omega⟩ := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := block_07 m i
    rw [he] at hb
    exact hb

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
