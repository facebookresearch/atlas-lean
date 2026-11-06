/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhMonomialSigns
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-! The two actual triangle-sign constraints have ten freely chosen Golay coefficients.
This counts original matrix-preserving signs, without claiming full-axis fixation. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The original two triangle-sign syndrome rows. -/
def generatedSeventhSignParameterRows : Fin 2 → ℕ :=
  ![1504, 1648]

/-- The exact binary linear syndrome matrix. -/
def generatedSeventhSignParameterMatrix : Matrix (Fin 2) (Fin 12) (ZMod 2) :=
  fun i j => if (generatedSeventhSignParameterRows i).testBit j.val then 1 else 0

/-- The ten free Golay coordinates reconstruct all twelve coefficients. -/
def generatedSeventhSignParameterEmbeddingRows : Fin 12 → ℕ :=
  ![1, 2, 4, 8, 224, 368, 16, 32, 64, 128, 256, 512]

/-- The exact binary reconstruction matrix. -/
def generatedSeventhSignParameterEmbedding : Matrix (Fin 12) (Fin 10) (ZMod 2) :=
  fun i j => if (generatedSeventhSignParameterEmbeddingRows i).testBit j.val then 1 else 0

/-- Projection to the ten free original Golay coefficient coordinates. -/
def generatedSeventhSignParameterProjectionRows : Fin 10 → ℕ :=
  ![1, 2, 4, 8, 64, 128, 256, 512, 1024, 2048]

/-- The exact binary free-coordinate projection matrix. -/
def generatedSeventhSignParameterProjection : Matrix (Fin 10) (Fin 12) (ZMod 2) :=
  fun i j => if (generatedSeventhSignParameterProjectionRows i).testBit j.val then 1 else 0

/-- Literal source-row combinations certify the full linear reconstruction. -/
def generatedSeventhSignParameterReconstructionRows : Fin 12 → ℕ :=
  ![0, 0, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0]

/-- The exact binary matrix of source-row combinations. -/
def generatedSeventhSignParameterReconstruction : Matrix (Fin 12) (Fin 2) (ZMod 2) :=
  fun i j => if (generatedSeventhSignParameterReconstructionRows i).testBit j.val then 1 else 0

-- The kernel checks every entry of the displayed finite binary matrix identity.
/-- Every embedded parameter vector has zero syndrome. -/
theorem generatedSeventhSignParameter_embedding_zero :
    generatedSeventhSignParameterMatrix * generatedSeventhSignParameterEmbedding = 0 := by
  decide +kernel

-- The kernel checks every entry of the displayed finite binary matrix identity.
/-- The free coordinates are recovered exactly. -/
theorem generatedSeventhSignParameter_projection_embedding :
    generatedSeventhSignParameterProjection * generatedSeventhSignParameterEmbedding = 1 := by
  decide +kernel

-- The kernel checks every entry of the displayed finite binary matrix identity.
/-- Embedding after projection differs from identity by literal syndrome rows. -/
theorem generatedSeventhSignParameter_reconstruction :
    generatedSeventhSignParameterEmbedding * generatedSeventhSignParameterProjection +
      generatedSeventhSignParameterReconstruction * generatedSeventhSignParameterMatrix = 1 := by
  decide +kernel

/-- The exact linear space of parameters with all displayed syndromes zero. -/
def generatedSeventhSignParameterSpace : Submodule (ZMod 2) (Fin 12 → ZMod 2) :=
  (Matrix.toLin' generatedSeventhSignParameterMatrix).ker

/-- An explicit bijection with ten freely chosen binary Golay coefficients. -/
def generatedSeventhSignParameterEquiv :
    generatedSeventhSignParameterSpace ≃ (Fin 10 → ZMod 2) where
  toFun w := generatedSeventhSignParameterProjection *ᵥ w.val
  invFun v := ⟨generatedSeventhSignParameterEmbedding *ᵥ v, by
    change generatedSeventhSignParameterMatrix *ᵥ (generatedSeventhSignParameterEmbedding *ᵥ v) = 0
    rw [Matrix.mulVec_mulVec, generatedSeventhSignParameter_embedding_zero, Matrix.zero_mulVec]⟩
  left_inv w := by
    apply Subtype.ext
    change generatedSeventhSignParameterEmbedding *ᵥ
      (generatedSeventhSignParameterProjection *ᵥ w.val) = w.val
    have hw : generatedSeventhSignParameterMatrix *ᵥ w.val = 0 := w.property
    have h : generatedSeventhSignParameterEmbedding *ᵥ
          (generatedSeventhSignParameterProjection *ᵥ w.val) +
        generatedSeventhSignParameterReconstruction *ᵥ
          (generatedSeventhSignParameterMatrix *ᵥ w.val) = w.val := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec,
        generatedSeventhSignParameter_reconstruction, Matrix.one_mulVec]
    simpa only [hw, Matrix.mulVec_zero, add_zero] using h
  right_inv v := by
    change generatedSeventhSignParameterProjection *ᵥ
      (generatedSeventhSignParameterEmbedding *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, generatedSeventhSignParameter_projection_embedding, Matrix.one_mulVec]

/-- Exactly 1024 Golay coefficient choices have both original triangle-sign syndromes zero. -/
theorem generatedSeventhSignParameterSpace_card :
    Nat.card generatedSeventhSignParameterSpace = 1024 := by
  rw [Nat.card_congr generatedSeventhSignParameterEquiv, Nat.card_eq_fintype_card, Fintype.card_fun]
  norm_num [ZMod.card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
