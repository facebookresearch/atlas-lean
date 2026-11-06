/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMathieuReducedTensorActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalTensorCacheData

/-! Exact finite certificates preserve all source spin addresses, phases, and tensor zeros. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Computable expressions evaluate the complete original address and both original signs. -/
def generatedRootEightMathieuReducedTensorCachedCoordinateCondition (j : Fin 2) (n : Fin 4096) : Prop :=
  generatedRootEightMathieuReducedTensorAddress j n =
    ⟨generatedNinthLowerSpinLabelMatrixFast
      (generatedRootEightMathieuReducedTensorRightInverseColumns j)
      (generatedRootEightMathieuReducedTensorTranslatedLabel j n).val % 4096,
        Nat.mod_lt _ (by decide)⟩ ∧
  generatedRootEightMathieuReducedTensorSign j n =
    (nortonUIntegerSign (toAdd (generatedRootEightMathieuReducedTensorPauli j).coeff) *
      (if (generatedNinthLowerSpinFastDotTwelve
        (nortonUIntegerLabel (spinModulation (generatedRootEightMathieuReducedTensorPauli j))).val
          n.val).testBit 0 then (-1 : ℤ) else 1)) *
      (if (generatedNinthLowerSpinQuadraticFast
        (generatedRootEightMathieuReducedTensorPhaseRows j)
        (generatedRootEightMathieuReducedTensorTranslatedLabel j n).val).testBit 0 then (-1 : ℤ) else 1)

/-- The cached finite expression has exactly the genuine phase-sensitive meaning. -/
theorem generatedRootEight_mathieu_reduced_tensor_coordinate_of_cached (j : Fin 2) (n : Fin 4096)
    (h : generatedRootEightMathieuReducedTensorCachedCoordinateCondition j n) :
    generatedRootEightMathieuReducedTensorCoordinateCondition j n := by
  unfold generatedRootEightMathieuReducedTensorCachedCoordinateCondition at h
  unfold generatedRootEightMathieuReducedTensorCoordinateCondition
  rw [generatedRootEight_mathieu_reduced_tensor_address_fast,
    generatedTwelfth_spin_pauli_sign_fast, generatedNinth_lower_spin_quadratic_fast_sign]
  exact h

set_option maxHeartbeats 16000000 in
-- Every coordinate in this bounded block includes its complete original sign.
private theorem address_block_00 : ∀ j : Fin 2, ∀ n : Fin 256,
    generatedRootEightMathieuReducedTensorCoordinateCondition j ⟨0 + n.val, by omega⟩ := by
  have hc : ∀ j : Fin 2, ∀ n : Fin 256,
      generatedRootEightMathieuReducedTensorCachedCoordinateCondition j ⟨0 + n.val, by omega⟩ := by
    unfold generatedRootEightMathieuReducedTensorCachedCoordinateCondition
    decide +kernel
  intro j n
  exact generatedRootEight_mathieu_reduced_tensor_coordinate_of_cached _ _ (hc j n)

set_option maxHeartbeats 16000000 in
-- Every coordinate in this bounded block includes its complete original sign.
private theorem address_block_01 : ∀ j : Fin 2, ∀ n : Fin 256,
    generatedRootEightMathieuReducedTensorCoordinateCondition j ⟨256 + n.val, by omega⟩ := by
  have hc : ∀ j : Fin 2, ∀ n : Fin 256,
      generatedRootEightMathieuReducedTensorCachedCoordinateCondition j ⟨256 + n.val, by omega⟩ := by
    unfold generatedRootEightMathieuReducedTensorCachedCoordinateCondition
    decide +kernel
  intro j n
  exact generatedRootEight_mathieu_reduced_tensor_coordinate_of_cached _ _ (hc j n)

set_option maxHeartbeats 16000000 in
-- Every coordinate in this bounded block includes its complete original sign.
private theorem address_block_02 : ∀ j : Fin 2, ∀ n : Fin 256,
    generatedRootEightMathieuReducedTensorCoordinateCondition j ⟨512 + n.val, by omega⟩ := by
  have hc : ∀ j : Fin 2, ∀ n : Fin 256,
      generatedRootEightMathieuReducedTensorCachedCoordinateCondition j ⟨512 + n.val, by omega⟩ := by
    unfold generatedRootEightMathieuReducedTensorCachedCoordinateCondition
    decide +kernel
  intro j n
  exact generatedRootEight_mathieu_reduced_tensor_coordinate_of_cached _ _ (hc j n)

set_option maxHeartbeats 16000000 in
-- Every coordinate in this bounded block includes its complete original sign.
private theorem address_block_03 : ∀ j : Fin 2, ∀ n : Fin 256,
    generatedRootEightMathieuReducedTensorCoordinateCondition j ⟨768 + n.val, by omega⟩ := by
  have hc : ∀ j : Fin 2, ∀ n : Fin 256,
      generatedRootEightMathieuReducedTensorCachedCoordinateCondition j ⟨768 + n.val, by omega⟩ := by
    unfold generatedRootEightMathieuReducedTensorCachedCoordinateCondition
    decide +kernel
  intro j n
  exact generatedRootEight_mathieu_reduced_tensor_coordinate_of_cached _ _ (hc j n)

set_option maxHeartbeats 16000000 in
-- Every coordinate in this bounded block includes its complete original sign.
private theorem address_block_04 : ∀ j : Fin 2, ∀ n : Fin 256,
    generatedRootEightMathieuReducedTensorCoordinateCondition j ⟨1024 + n.val, by omega⟩ := by
  have hc : ∀ j : Fin 2, ∀ n : Fin 256,
      generatedRootEightMathieuReducedTensorCachedCoordinateCondition j ⟨1024 + n.val, by omega⟩ := by
    unfold generatedRootEightMathieuReducedTensorCachedCoordinateCondition
    decide +kernel
  intro j n
  exact generatedRootEight_mathieu_reduced_tensor_coordinate_of_cached _ _ (hc j n)

set_option maxHeartbeats 16000000 in
-- Every coordinate in this bounded block includes its complete original sign.
private theorem address_block_05 : ∀ j : Fin 2, ∀ n : Fin 256,
    generatedRootEightMathieuReducedTensorCoordinateCondition j ⟨1280 + n.val, by omega⟩ := by
  have hc : ∀ j : Fin 2, ∀ n : Fin 256,
      generatedRootEightMathieuReducedTensorCachedCoordinateCondition j ⟨1280 + n.val, by omega⟩ := by
    unfold generatedRootEightMathieuReducedTensorCachedCoordinateCondition
    decide +kernel
  intro j n
  exact generatedRootEight_mathieu_reduced_tensor_coordinate_of_cached _ _ (hc j n)

set_option maxHeartbeats 16000000 in
-- Every coordinate in this bounded block includes its complete original sign.
private theorem address_block_06 : ∀ j : Fin 2, ∀ n : Fin 256,
    generatedRootEightMathieuReducedTensorCoordinateCondition j ⟨1536 + n.val, by omega⟩ := by
  have hc : ∀ j : Fin 2, ∀ n : Fin 256,
      generatedRootEightMathieuReducedTensorCachedCoordinateCondition j ⟨1536 + n.val, by omega⟩ := by
    unfold generatedRootEightMathieuReducedTensorCachedCoordinateCondition
    decide +kernel
  intro j n
  exact generatedRootEight_mathieu_reduced_tensor_coordinate_of_cached _ _ (hc j n)

set_option maxHeartbeats 16000000 in
-- Every coordinate in this bounded block includes its complete original sign.
private theorem address_block_07 : ∀ j : Fin 2, ∀ n : Fin 256,
    generatedRootEightMathieuReducedTensorCoordinateCondition j ⟨1792 + n.val, by omega⟩ := by
  have hc : ∀ j : Fin 2, ∀ n : Fin 256,
      generatedRootEightMathieuReducedTensorCachedCoordinateCondition j ⟨1792 + n.val, by omega⟩ := by
    unfold generatedRootEightMathieuReducedTensorCachedCoordinateCondition
    decide +kernel
  intro j n
  exact generatedRootEight_mathieu_reduced_tensor_coordinate_of_cached _ _ (hc j n)

set_option maxHeartbeats 16000000 in
-- Every coordinate in this bounded block includes its complete original sign.
private theorem address_block_08 : ∀ j : Fin 2, ∀ n : Fin 256,
    generatedRootEightMathieuReducedTensorCoordinateCondition j ⟨2048 + n.val, by omega⟩ := by
  have hc : ∀ j : Fin 2, ∀ n : Fin 256,
      generatedRootEightMathieuReducedTensorCachedCoordinateCondition j ⟨2048 + n.val, by omega⟩ := by
    unfold generatedRootEightMathieuReducedTensorCachedCoordinateCondition
    decide +kernel
  intro j n
  exact generatedRootEight_mathieu_reduced_tensor_coordinate_of_cached _ _ (hc j n)

set_option maxHeartbeats 16000000 in
-- Every coordinate in this bounded block includes its complete original sign.
private theorem address_block_09 : ∀ j : Fin 2, ∀ n : Fin 256,
    generatedRootEightMathieuReducedTensorCoordinateCondition j ⟨2304 + n.val, by omega⟩ := by
  have hc : ∀ j : Fin 2, ∀ n : Fin 256,
      generatedRootEightMathieuReducedTensorCachedCoordinateCondition j ⟨2304 + n.val, by omega⟩ := by
    unfold generatedRootEightMathieuReducedTensorCachedCoordinateCondition
    decide +kernel
  intro j n
  exact generatedRootEight_mathieu_reduced_tensor_coordinate_of_cached _ _ (hc j n)

set_option maxHeartbeats 16000000 in
-- Every coordinate in this bounded block includes its complete original sign.
private theorem address_block_10 : ∀ j : Fin 2, ∀ n : Fin 256,
    generatedRootEightMathieuReducedTensorCoordinateCondition j ⟨2560 + n.val, by omega⟩ := by
  have hc : ∀ j : Fin 2, ∀ n : Fin 256,
      generatedRootEightMathieuReducedTensorCachedCoordinateCondition j ⟨2560 + n.val, by omega⟩ := by
    unfold generatedRootEightMathieuReducedTensorCachedCoordinateCondition
    decide +kernel
  intro j n
  exact generatedRootEight_mathieu_reduced_tensor_coordinate_of_cached _ _ (hc j n)

set_option maxHeartbeats 16000000 in
-- Every coordinate in this bounded block includes its complete original sign.
private theorem address_block_11 : ∀ j : Fin 2, ∀ n : Fin 256,
    generatedRootEightMathieuReducedTensorCoordinateCondition j ⟨2816 + n.val, by omega⟩ := by
  have hc : ∀ j : Fin 2, ∀ n : Fin 256,
      generatedRootEightMathieuReducedTensorCachedCoordinateCondition j ⟨2816 + n.val, by omega⟩ := by
    unfold generatedRootEightMathieuReducedTensorCachedCoordinateCondition
    decide +kernel
  intro j n
  exact generatedRootEight_mathieu_reduced_tensor_coordinate_of_cached _ _ (hc j n)

set_option maxHeartbeats 16000000 in
-- Every coordinate in this bounded block includes its complete original sign.
private theorem address_block_12 : ∀ j : Fin 2, ∀ n : Fin 256,
    generatedRootEightMathieuReducedTensorCoordinateCondition j ⟨3072 + n.val, by omega⟩ := by
  have hc : ∀ j : Fin 2, ∀ n : Fin 256,
      generatedRootEightMathieuReducedTensorCachedCoordinateCondition j ⟨3072 + n.val, by omega⟩ := by
    unfold generatedRootEightMathieuReducedTensorCachedCoordinateCondition
    decide +kernel
  intro j n
  exact generatedRootEight_mathieu_reduced_tensor_coordinate_of_cached _ _ (hc j n)

set_option maxHeartbeats 16000000 in
-- Every coordinate in this bounded block includes its complete original sign.
private theorem address_block_13 : ∀ j : Fin 2, ∀ n : Fin 256,
    generatedRootEightMathieuReducedTensorCoordinateCondition j ⟨3328 + n.val, by omega⟩ := by
  have hc : ∀ j : Fin 2, ∀ n : Fin 256,
      generatedRootEightMathieuReducedTensorCachedCoordinateCondition j ⟨3328 + n.val, by omega⟩ := by
    unfold generatedRootEightMathieuReducedTensorCachedCoordinateCondition
    decide +kernel
  intro j n
  exact generatedRootEight_mathieu_reduced_tensor_coordinate_of_cached _ _ (hc j n)

set_option maxHeartbeats 16000000 in
-- Every coordinate in this bounded block includes its complete original sign.
private theorem address_block_14 : ∀ j : Fin 2, ∀ n : Fin 256,
    generatedRootEightMathieuReducedTensorCoordinateCondition j ⟨3584 + n.val, by omega⟩ := by
  have hc : ∀ j : Fin 2, ∀ n : Fin 256,
      generatedRootEightMathieuReducedTensorCachedCoordinateCondition j ⟨3584 + n.val, by omega⟩ := by
    unfold generatedRootEightMathieuReducedTensorCachedCoordinateCondition
    decide +kernel
  intro j n
  exact generatedRootEight_mathieu_reduced_tensor_coordinate_of_cached _ _ (hc j n)

set_option maxHeartbeats 16000000 in
-- Every coordinate in this bounded block includes its complete original sign.
private theorem address_block_15 : ∀ j : Fin 2, ∀ n : Fin 256,
    generatedRootEightMathieuReducedTensorCoordinateCondition j ⟨3840 + n.val, by omega⟩ := by
  have hc : ∀ j : Fin 2, ∀ n : Fin 256,
      generatedRootEightMathieuReducedTensorCachedCoordinateCondition j ⟨3840 + n.val, by omega⟩ := by
    unfold generatedRootEightMathieuReducedTensorCachedCoordinateCondition
    decide +kernel
  intro j n
  exact generatedRootEight_mathieu_reduced_tensor_coordinate_of_cached _ _ (hc j n)

/-- Every original label and full central/quadratic sign is certified for both reduced models. -/
theorem generatedRootEight_mathieu_reduced_tensor_coordinate_certificate (j : Fin 2) (n : Fin 4096) :
    generatedRootEightMathieuReducedTensorCoordinateCondition j n := by
  have hq : n.val / 256 < 16 := by omega
  interval_cases h : n.val / 256
  · let m : Fin 256 := ⟨n.val - 0, by omega⟩
    have he : (⟨0 + m.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := address_block_00 j m
    rw [he] at hb
    exact hb
  · let m : Fin 256 := ⟨n.val - 256, by omega⟩
    have he : (⟨256 + m.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := address_block_01 j m
    rw [he] at hb
    exact hb
  · let m : Fin 256 := ⟨n.val - 512, by omega⟩
    have he : (⟨512 + m.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := address_block_02 j m
    rw [he] at hb
    exact hb
  · let m : Fin 256 := ⟨n.val - 768, by omega⟩
    have he : (⟨768 + m.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := address_block_03 j m
    rw [he] at hb
    exact hb
  · let m : Fin 256 := ⟨n.val - 1024, by omega⟩
    have he : (⟨1024 + m.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := address_block_04 j m
    rw [he] at hb
    exact hb
  · let m : Fin 256 := ⟨n.val - 1280, by omega⟩
    have he : (⟨1280 + m.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := address_block_05 j m
    rw [he] at hb
    exact hb
  · let m : Fin 256 := ⟨n.val - 1536, by omega⟩
    have he : (⟨1536 + m.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := address_block_06 j m
    rw [he] at hb
    exact hb
  · let m : Fin 256 := ⟨n.val - 1792, by omega⟩
    have he : (⟨1792 + m.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := address_block_07 j m
    rw [he] at hb
    exact hb
  · let m : Fin 256 := ⟨n.val - 2048, by omega⟩
    have he : (⟨2048 + m.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := address_block_08 j m
    rw [he] at hb
    exact hb
  · let m : Fin 256 := ⟨n.val - 2304, by omega⟩
    have he : (⟨2304 + m.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := address_block_09 j m
    rw [he] at hb
    exact hb
  · let m : Fin 256 := ⟨n.val - 2560, by omega⟩
    have he : (⟨2560 + m.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := address_block_10 j m
    rw [he] at hb
    exact hb
  · let m : Fin 256 := ⟨n.val - 2816, by omega⟩
    have he : (⟨2816 + m.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := address_block_11 j m
    rw [he] at hb
    exact hb
  · let m : Fin 256 := ⟨n.val - 3072, by omega⟩
    have he : (⟨3072 + m.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := address_block_12 j m
    rw [he] at hb
    exact hb
  · let m : Fin 256 := ⟨n.val - 3328, by omega⟩
    have he : (⟨3328 + m.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := address_block_13 j m
    rw [he] at hb
    exact hb
  · let m : Fin 256 := ⟨n.val - 3584, by omega⟩
    have he : (⟨3584 + m.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := address_block_14 j m
    rw [he] at hb
    exact hb
  · let m : Fin 256 := ⟨n.val - 3840, by omega⟩
    have he : (⟨3840 + m.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := address_block_15 j m
    rw [he] at hb
    exact hb

/-- Every cached tensor coordinate is fixed, including every zero entry and its original sign. -/
def generatedRootEightMathieuReducedTensorCachedFixCondition (j : Fin 2) (n : Fin 4096) (i : Fin 24) : Prop :=
  generatedRootEightMathieuReducedTensorSign j n *
    generatedRootEightCanonicalTensorCache (generatedRootEightMathieuReducedTensorAddress j n)
      (generatedRootEightMathieuReducedInverse j i) =
    generatedRootEightCanonicalTensorCache n i

set_option maxHeartbeats 16000000 in
-- The whole original target tensor is checked; no support subset is omitted.
private theorem tensor_block_00 : ∀ j : Fin 2, ∀ n : Fin 256, ∀ i : Fin 24,
    generatedRootEightMathieuReducedTensorCachedFixCondition j ⟨0 + n.val, by omega⟩ i := by
  unfold generatedRootEightMathieuReducedTensorCachedFixCondition
  decide +kernel

set_option maxHeartbeats 16000000 in
-- The whole original target tensor is checked; no support subset is omitted.
private theorem tensor_block_01 : ∀ j : Fin 2, ∀ n : Fin 256, ∀ i : Fin 24,
    generatedRootEightMathieuReducedTensorCachedFixCondition j ⟨256 + n.val, by omega⟩ i := by
  unfold generatedRootEightMathieuReducedTensorCachedFixCondition
  decide +kernel

set_option maxHeartbeats 16000000 in
-- The whole original target tensor is checked; no support subset is omitted.
private theorem tensor_block_02 : ∀ j : Fin 2, ∀ n : Fin 256, ∀ i : Fin 24,
    generatedRootEightMathieuReducedTensorCachedFixCondition j ⟨512 + n.val, by omega⟩ i := by
  unfold generatedRootEightMathieuReducedTensorCachedFixCondition
  decide +kernel

set_option maxHeartbeats 16000000 in
-- The whole original target tensor is checked; no support subset is omitted.
private theorem tensor_block_03 : ∀ j : Fin 2, ∀ n : Fin 256, ∀ i : Fin 24,
    generatedRootEightMathieuReducedTensorCachedFixCondition j ⟨768 + n.val, by omega⟩ i := by
  unfold generatedRootEightMathieuReducedTensorCachedFixCondition
  decide +kernel

set_option maxHeartbeats 16000000 in
-- The whole original target tensor is checked; no support subset is omitted.
private theorem tensor_block_04 : ∀ j : Fin 2, ∀ n : Fin 256, ∀ i : Fin 24,
    generatedRootEightMathieuReducedTensorCachedFixCondition j ⟨1024 + n.val, by omega⟩ i := by
  unfold generatedRootEightMathieuReducedTensorCachedFixCondition
  decide +kernel

set_option maxHeartbeats 16000000 in
-- The whole original target tensor is checked; no support subset is omitted.
private theorem tensor_block_05 : ∀ j : Fin 2, ∀ n : Fin 256, ∀ i : Fin 24,
    generatedRootEightMathieuReducedTensorCachedFixCondition j ⟨1280 + n.val, by omega⟩ i := by
  unfold generatedRootEightMathieuReducedTensorCachedFixCondition
  decide +kernel

set_option maxHeartbeats 16000000 in
-- The whole original target tensor is checked; no support subset is omitted.
private theorem tensor_block_06 : ∀ j : Fin 2, ∀ n : Fin 256, ∀ i : Fin 24,
    generatedRootEightMathieuReducedTensorCachedFixCondition j ⟨1536 + n.val, by omega⟩ i := by
  unfold generatedRootEightMathieuReducedTensorCachedFixCondition
  decide +kernel

set_option maxHeartbeats 16000000 in
-- The whole original target tensor is checked; no support subset is omitted.
private theorem tensor_block_07 : ∀ j : Fin 2, ∀ n : Fin 256, ∀ i : Fin 24,
    generatedRootEightMathieuReducedTensorCachedFixCondition j ⟨1792 + n.val, by omega⟩ i := by
  unfold generatedRootEightMathieuReducedTensorCachedFixCondition
  decide +kernel

set_option maxHeartbeats 16000000 in
-- The whole original target tensor is checked; no support subset is omitted.
private theorem tensor_block_08 : ∀ j : Fin 2, ∀ n : Fin 256, ∀ i : Fin 24,
    generatedRootEightMathieuReducedTensorCachedFixCondition j ⟨2048 + n.val, by omega⟩ i := by
  unfold generatedRootEightMathieuReducedTensorCachedFixCondition
  decide +kernel

set_option maxHeartbeats 16000000 in
-- The whole original target tensor is checked; no support subset is omitted.
private theorem tensor_block_09 : ∀ j : Fin 2, ∀ n : Fin 256, ∀ i : Fin 24,
    generatedRootEightMathieuReducedTensorCachedFixCondition j ⟨2304 + n.val, by omega⟩ i := by
  unfold generatedRootEightMathieuReducedTensorCachedFixCondition
  decide +kernel

set_option maxHeartbeats 16000000 in
-- The whole original target tensor is checked; no support subset is omitted.
private theorem tensor_block_10 : ∀ j : Fin 2, ∀ n : Fin 256, ∀ i : Fin 24,
    generatedRootEightMathieuReducedTensorCachedFixCondition j ⟨2560 + n.val, by omega⟩ i := by
  unfold generatedRootEightMathieuReducedTensorCachedFixCondition
  decide +kernel

set_option maxHeartbeats 16000000 in
-- The whole original target tensor is checked; no support subset is omitted.
private theorem tensor_block_11 : ∀ j : Fin 2, ∀ n : Fin 256, ∀ i : Fin 24,
    generatedRootEightMathieuReducedTensorCachedFixCondition j ⟨2816 + n.val, by omega⟩ i := by
  unfold generatedRootEightMathieuReducedTensorCachedFixCondition
  decide +kernel

set_option maxHeartbeats 16000000 in
-- The whole original target tensor is checked; no support subset is omitted.
private theorem tensor_block_12 : ∀ j : Fin 2, ∀ n : Fin 256, ∀ i : Fin 24,
    generatedRootEightMathieuReducedTensorCachedFixCondition j ⟨3072 + n.val, by omega⟩ i := by
  unfold generatedRootEightMathieuReducedTensorCachedFixCondition
  decide +kernel

set_option maxHeartbeats 16000000 in
-- The whole original target tensor is checked; no support subset is omitted.
private theorem tensor_block_13 : ∀ j : Fin 2, ∀ n : Fin 256, ∀ i : Fin 24,
    generatedRootEightMathieuReducedTensorCachedFixCondition j ⟨3328 + n.val, by omega⟩ i := by
  unfold generatedRootEightMathieuReducedTensorCachedFixCondition
  decide +kernel

set_option maxHeartbeats 16000000 in
-- The whole original target tensor is checked; no support subset is omitted.
private theorem tensor_block_14 : ∀ j : Fin 2, ∀ n : Fin 256, ∀ i : Fin 24,
    generatedRootEightMathieuReducedTensorCachedFixCondition j ⟨3584 + n.val, by omega⟩ i := by
  unfold generatedRootEightMathieuReducedTensorCachedFixCondition
  decide +kernel

set_option maxHeartbeats 16000000 in
-- The whole original target tensor is checked; no support subset is omitted.
private theorem tensor_block_15 : ∀ j : Fin 2, ∀ n : Fin 256, ∀ i : Fin 24,
    generatedRootEightMathieuReducedTensorCachedFixCondition j ⟨3840 + n.val, by omega⟩ i := by
  unfold generatedRootEightMathieuReducedTensorCachedFixCondition
  decide +kernel

/-- All 98,304 tensor coordinates are fixed by each actual rank-zero model. -/
theorem generatedRootEight_mathieu_reduced_tensor_cache_fixation (j : Fin 2) (n : Fin 4096) (i : Fin 24) :
    generatedRootEightMathieuReducedTensorCachedFixCondition j n i := by
  have hq : n.val / 256 < 16 := by omega
  interval_cases h : n.val / 256
  · let m : Fin 256 := ⟨n.val - 0, by omega⟩
    have he : (⟨0 + m.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := tensor_block_00 j m i
    rw [he] at hb
    exact hb
  · let m : Fin 256 := ⟨n.val - 256, by omega⟩
    have he : (⟨256 + m.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := tensor_block_01 j m i
    rw [he] at hb
    exact hb
  · let m : Fin 256 := ⟨n.val - 512, by omega⟩
    have he : (⟨512 + m.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := tensor_block_02 j m i
    rw [he] at hb
    exact hb
  · let m : Fin 256 := ⟨n.val - 768, by omega⟩
    have he : (⟨768 + m.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := tensor_block_03 j m i
    rw [he] at hb
    exact hb
  · let m : Fin 256 := ⟨n.val - 1024, by omega⟩
    have he : (⟨1024 + m.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := tensor_block_04 j m i
    rw [he] at hb
    exact hb
  · let m : Fin 256 := ⟨n.val - 1280, by omega⟩
    have he : (⟨1280 + m.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := tensor_block_05 j m i
    rw [he] at hb
    exact hb
  · let m : Fin 256 := ⟨n.val - 1536, by omega⟩
    have he : (⟨1536 + m.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := tensor_block_06 j m i
    rw [he] at hb
    exact hb
  · let m : Fin 256 := ⟨n.val - 1792, by omega⟩
    have he : (⟨1792 + m.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := tensor_block_07 j m i
    rw [he] at hb
    exact hb
  · let m : Fin 256 := ⟨n.val - 2048, by omega⟩
    have he : (⟨2048 + m.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := tensor_block_08 j m i
    rw [he] at hb
    exact hb
  · let m : Fin 256 := ⟨n.val - 2304, by omega⟩
    have he : (⟨2304 + m.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := tensor_block_09 j m i
    rw [he] at hb
    exact hb
  · let m : Fin 256 := ⟨n.val - 2560, by omega⟩
    have he : (⟨2560 + m.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := tensor_block_10 j m i
    rw [he] at hb
    exact hb
  · let m : Fin 256 := ⟨n.val - 2816, by omega⟩
    have he : (⟨2816 + m.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := tensor_block_11 j m i
    rw [he] at hb
    exact hb
  · let m : Fin 256 := ⟨n.val - 3072, by omega⟩
    have he : (⟨3072 + m.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := tensor_block_12 j m i
    rw [he] at hb
    exact hb
  · let m : Fin 256 := ⟨n.val - 3328, by omega⟩
    have he : (⟨3328 + m.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := tensor_block_13 j m i
    rw [he] at hb
    exact hb
  · let m : Fin 256 := ⟨n.val - 3584, by omega⟩
    have he : (⟨3584 + m.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := tensor_block_14 j m i
    rw [he] at hb
    exact hb
  · let m : Fin 256 := ⟨n.val - 3840, by omega⟩
    have he : (⟨3840 + m.val, by omega⟩ : Fin 4096) = n := by
      apply Fin.ext
      dsimp only [m]
      omega
    have hb := tensor_block_15 j m i
    rw [he] at hb
    exact hb

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
