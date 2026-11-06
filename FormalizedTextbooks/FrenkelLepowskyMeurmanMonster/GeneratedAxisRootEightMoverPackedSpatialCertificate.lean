/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverPackedSpatialBlock00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverPackedSpatialBlock01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverPackedSpatialBlock02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverPackedSpatialBlock03

/-! Exact original mover tensor boundaries and positive spatial coefficients. -/
@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- All complete positive spatial rows and original tensor word prefixes are checked. -/
theorem generatedRootEight_mover_packed_spatial_certificate (i : Fin 24) (a : Fin 256) :
    generatedRootEightMoverPackedSpatialCondition i a := by
  by_cases h0 : i.val < 6
  · let u : Fin 6 := ⟨i.val - 0, by omega⟩
    have hi : (⟨u.val + 0, by omega⟩ : Fin 24) = i := by
      apply Fin.ext
      dsimp [u] <;> omega
    have h := generatedRootEight_mover_packed_spatial_block_00 u a
    rw [hi] at h
    exact h
  by_cases h1 : i.val < 12
  · let u : Fin 6 := ⟨i.val - 6, by omega⟩
    have hi : (⟨u.val + 6, by omega⟩ : Fin 24) = i := by
      apply Fin.ext
      dsimp [u] <;> omega
    have h := generatedRootEight_mover_packed_spatial_block_01 u a
    rw [hi] at h
    exact h
  by_cases h2 : i.val < 18
  · let u : Fin 6 := ⟨i.val - 12, by omega⟩
    have hi : (⟨u.val + 12, by omega⟩ : Fin 24) = i := by
      apply Fin.ext
      dsimp [u] <;> omega
    have h := generatedRootEight_mover_packed_spatial_block_02 u a
    rw [hi] at h
    exact h
  let u : Fin 6 := ⟨i.val - 18, by omega⟩
  have hi : (⟨u.val + 18, by omega⟩ : Fin 24) = i := by
    apply Fin.ext
    dsimp [u] <;> omega
  have h := generatedRootEight_mover_packed_spatial_block_03 u a
  rw [hi] at h
  exact h

/-- The actual positive spatial numerator fixes the full final tensor with its exact scale64. -/
theorem generatedRootEight_mover_tensor_spatial_integer (n : Fin 4096) (i : Fin 24) :
    (∑ j : Fin 24, generatedRootEightMoverSpatialNumerator i j *
      generatedRootEightMoverTensorFinalInteger n j) =
        64 * generatedRootEightMoverTensorSourceInteger n i :=
  generatedRootEight_mover_packed_spatial_of_condition
    generatedRootEight_mover_packed_spatial_certificate n i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
