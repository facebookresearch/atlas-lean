/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverTensorLowPair01Block00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverTensorLowPair01Block01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverTensorLowPair01Block02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverTensorLowPair01Block03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverTensorLowPair02Block00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverTensorLowPair02Block01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverTensorLowPair02Block02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverTensorLowPair02Block03

/-! Complete original corrected mover low-pair word checks, including every signed slot. -/
@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- The complete actual low pair is checked on every physical column and word prefix. -/
theorem generatedRootEight_mover_tensor_low_pair_01_certificate (j : Fin 24) (a : Fin 256) :
    generatedRootEightMoverTensorLowPairCondition 1 2 3 j a := by
  by_cases h0 : j.val < 6
  · let u : Fin 6 := ⟨j.val - 0, by omega⟩
    have hj : (⟨u.val + 0, by omega⟩ : Fin 24) = j := by
      apply Fin.ext
      dsimp [u] <;> omega
    have h := generatedRootEight_mover_tensor_low_pair_01_block_00 u a
    rw [hj] at h
    exact h
  by_cases h1 : j.val < 12
  · let u : Fin 6 := ⟨j.val - 6, by omega⟩
    have hj : (⟨u.val + 6, by omega⟩ : Fin 24) = j := by
      apply Fin.ext
      dsimp [u] <;> omega
    have h := generatedRootEight_mover_tensor_low_pair_01_block_01 u a
    rw [hj] at h
    exact h
  by_cases h2 : j.val < 18
  · let u : Fin 6 := ⟨j.val - 12, by omega⟩
    have hj : (⟨u.val + 12, by omega⟩ : Fin 24) = j := by
      apply Fin.ext
      dsimp [u] <;> omega
    have h := generatedRootEight_mover_tensor_low_pair_01_block_02 u a
    rw [hj] at h
    exact h
  let u : Fin 6 := ⟨j.val - 18, by omega⟩
  have hj : (⟨u.val + 18, by omega⟩ : Fin 24) = j := by
    apply Fin.ext
    dsimp [u] <;> omega
  have h := generatedRootEight_mover_tensor_low_pair_01_block_03 u a
  rw [hj] at h
  exact h

/-- The actual corrected mover low pair is proved on every original4096 label and physical column. -/
theorem generatedRootEight_mover_tensor_pair_01 (j : Fin 24) : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorFourierInteger 2
      (generatedNinthLowerSpinTensorFourierInteger 3
        (generatedRootEightMoverTensorSpinInteger 1 j)) n =
      2 * generatedRootEightMoverTensorSpinInteger 2 j n := by
  exact generatedRootEight_mover_tensor_low_pair_of_condition 1 2 3 (by decide) j
    (generatedRootEight_mover_tensor_low_pair_01_certificate j)

/-- The complete actual low pair is checked on every physical column and word prefix. -/
theorem generatedRootEight_mover_tensor_low_pair_02_certificate (j : Fin 24) (a : Fin 256) :
    generatedRootEightMoverTensorLowPairCondition 2 0 1 j a := by
  by_cases h0 : j.val < 6
  · let u : Fin 6 := ⟨j.val - 0, by omega⟩
    have hj : (⟨u.val + 0, by omega⟩ : Fin 24) = j := by
      apply Fin.ext
      dsimp [u] <;> omega
    have h := generatedRootEight_mover_tensor_low_pair_02_block_00 u a
    rw [hj] at h
    exact h
  by_cases h1 : j.val < 12
  · let u : Fin 6 := ⟨j.val - 6, by omega⟩
    have hj : (⟨u.val + 6, by omega⟩ : Fin 24) = j := by
      apply Fin.ext
      dsimp [u] <;> omega
    have h := generatedRootEight_mover_tensor_low_pair_02_block_01 u a
    rw [hj] at h
    exact h
  by_cases h2 : j.val < 18
  · let u : Fin 6 := ⟨j.val - 12, by omega⟩
    have hj : (⟨u.val + 12, by omega⟩ : Fin 24) = j := by
      apply Fin.ext
      dsimp [u] <;> omega
    have h := generatedRootEight_mover_tensor_low_pair_02_block_02 u a
    rw [hj] at h
    exact h
  let u : Fin 6 := ⟨j.val - 18, by omega⟩
  have hj : (⟨u.val + 18, by omega⟩ : Fin 24) = j := by
    apply Fin.ext
    dsimp [u] <;> omega
  have h := generatedRootEight_mover_tensor_low_pair_02_block_03 u a
  rw [hj] at h
  exact h

/-- The actual corrected mover low pair is proved on every original4096 label and physical column. -/
theorem generatedRootEight_mover_tensor_pair_02 (j : Fin 24) : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorFourierInteger 0
      (generatedNinthLowerSpinTensorFourierInteger 1
        (generatedRootEightMoverTensorSpinInteger 2 j)) n =
      2 * generatedRootEightMoverTensorSpinInteger 3 j n := by
  exact generatedRootEight_mover_tensor_low_pair_of_condition 2 0 1 (by decide) j
    (generatedRootEight_mover_tensor_low_pair_02_certificate j)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
