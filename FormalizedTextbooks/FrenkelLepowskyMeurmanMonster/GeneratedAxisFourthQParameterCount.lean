/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Definitions
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Exact binary parameter count for the fourth tensor family's proposed syndrome system.
The relation to the original tensor is discharged separately by its coordinate binding. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The two plane-annihilator rows and twenty-two affine-family syndrome rows. -/
def generatedFourthQParameterRows : Fin 24 → ℕ :=
  ![56, 8192, 0, 16, 24, 8, 1237, 1221, 3269, 3277, 2269, 2245,
    3080, 3096, 3088, 3072, 1040, 1032, 1048, 1024, 2072, 2064, 2056, 2048]

/-- The exact binary linear syndrome matrix. -/
def generatedFourthQParameterMatrix : Matrix (Fin 24) (Fin 14) (ZMod 2) :=
  fun i j => if (generatedFourthQParameterRows i).testBit j.val then 1 else 0

/-- The seven free coordinates reconstruct all fourteen parameters. -/
def generatedFourthQParameterEmbeddingRows : Fin 14 → ℕ :=
  ![14, 1, 2, 0, 0, 0, 4, 8, 16, 32, 0, 0, 64, 0]

/-- The exact binary reconstruction matrix. -/
def generatedFourthQParameterEmbedding : Matrix (Fin 14) (Fin 7) (ZMod 2) :=
  fun i j => if (generatedFourthQParameterEmbeddingRows i).testBit j.val then 1 else 0

/-- Projection to the seven explicit free parameter coordinates. -/
def generatedFourthQParameterProjectionRows : Fin 7 → ℕ :=
  ![2, 4, 64, 128, 256, 512, 4096]

/-- The exact binary free-coordinate projection matrix. -/
def generatedFourthQParameterProjection : Matrix (Fin 7) (Fin 14) (ZMod 2) :=
  fun i j => if (generatedFourthQParameterProjectionRows i).testBit j.val then 1 else 0

/-- Literal source-row combinations certify the full linear reconstruction. -/
def generatedFourthQParameterReconstructionRows : Fin 14 → ℕ :=
  ![1368, 0, 0, 24, 8, 17, 0, 0, 0, 0, 1296, 328, 0, 2]

/-- The exact binary matrix of source-row combinations. -/
def generatedFourthQParameterReconstruction : Matrix (Fin 14) (Fin 24) (ZMod 2) :=
  fun i j => if (generatedFourthQParameterReconstructionRows i).testBit j.val then 1 else 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- The kernel checks every entry of the displayed finite binary matrix identity.
/-- Every embedded parameter vector has zero syndrome. -/
theorem generatedFourthQParameter_embedding_zero :
    generatedFourthQParameterMatrix * generatedFourthQParameterEmbedding = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- The kernel checks every entry of the displayed finite binary matrix identity.
/-- The free coordinates are recovered exactly. -/
theorem generatedFourthQParameter_projection_embedding :
    generatedFourthQParameterProjection * generatedFourthQParameterEmbedding = 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- The kernel checks every entry of the displayed finite binary matrix identity.
/-- Embedding after projection differs from identity by literal syndrome rows. -/
theorem generatedFourthQParameter_reconstruction :
    generatedFourthQParameterEmbedding * generatedFourthQParameterProjection +
      generatedFourthQParameterReconstruction * generatedFourthQParameterMatrix = 1 := by
  decide +kernel

/-- The exact linear space of parameters with all displayed syndromes zero. -/
def generatedFourthQParameterSpace : Submodule (ZMod 2) (Fin 14 → ZMod 2) :=
  (Matrix.toLin' generatedFourthQParameterMatrix).ker

/-- An explicit bijection with seven freely chosen binary parameters. -/
def generatedFourthQParameterEquiv : generatedFourthQParameterSpace ≃ (Fin 7 → ZMod 2) where
  toFun w := generatedFourthQParameterProjection *ᵥ w.val
  invFun v := ⟨generatedFourthQParameterEmbedding *ᵥ v, by
    change generatedFourthQParameterMatrix *ᵥ (generatedFourthQParameterEmbedding *ᵥ v) = 0
    rw [Matrix.mulVec_mulVec, generatedFourthQParameter_embedding_zero, Matrix.zero_mulVec]⟩
  left_inv w := by
    apply Subtype.ext
    change generatedFourthQParameterEmbedding *ᵥ (generatedFourthQParameterProjection *ᵥ w.val) =
      w.val
    have hw : generatedFourthQParameterMatrix *ᵥ w.val = 0 := w.property
    have h : generatedFourthQParameterEmbedding *ᵥ
          (generatedFourthQParameterProjection *ᵥ w.val) +
        generatedFourthQParameterReconstruction *ᵥ
          (generatedFourthQParameterMatrix *ᵥ w.val) = w.val := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec,
        generatedFourthQParameter_reconstruction, Matrix.one_mulVec]
    simpa only [hw, Matrix.mulVec_zero, add_zero] using h
  right_inv v := by
    change generatedFourthQParameterProjection *ᵥ (generatedFourthQParameterEmbedding *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, generatedFourthQParameter_projection_embedding, Matrix.one_mulVec]

/-- Exactly 128 binary parameter choices satisfy the complete syndrome system. -/
theorem generatedFourthQParameterSpace_card : Nat.card generatedFourthQParameterSpace = 128 := by
  rw [Nat.card_congr generatedFourthQParameterEquiv, Nat.card_eq_fintype_card, Fintype.card_fun]
  norm_num [ZMod.card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
