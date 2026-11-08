/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.InnerProductSpace.FiniteFrame

/-!
# Tests for finite frames

The constant frame on `ℂ` (two copies of `1` in a one-dimensional space) is a
tight frame with bounds `2, 2`: it is redundant, its frame operator is `2 • 1`,
its inverse frame operator is `(1 / 2) • 1`, its dual frame has bounds
`1 / 2, 1 / 2`, and reconstruction holds. An orthonormal basis is a frame with
bounds `1, 1`.
-/

namespace MathlibExtTest.Analysis.InnerProductSpace.FiniteFrameTests

open scoped _root_.InnerProductSpace
open MathlibExt.Analysis.InnerProductSpace.FiniteFrame

/-- The constant frame on `ℂ` is a tight frame with bounds `2, 2`. -/
theorem constFrame : IsFrame (𝕜 := ℂ) (fun _ : Fin 2 => (1 : ℂ)) 2 2 := by
  refine ⟨by norm_num, by norm_num, fun x => ?_⟩
  have hsum : ∑ _i : Fin 2, ‖⟪(1 : ℂ), x⟫_ℂ‖ ^ 2 = 2 * ‖x‖ ^ 2 := by
    rw [Fin.sum_univ_two]
    simp [RCLike.inner_apply]
    ring
  rw [hsum]
  exact ⟨le_rfl, le_rfl⟩

/-- The coefficient sums for the constant frame on `ℂ`. -/
example (x : ℂ) :
    ∑ _i : Fin 2, ‖⟪(1 : ℂ), x⟫_ℂ‖ ^ 2 = 2 * ‖x‖ ^ 2 := by
  rw [Fin.sum_univ_two]
  simp [RCLike.inner_apply]
  ring

/-- The frame operator of the constant frame on `ℂ` is `2 • 1`. -/
example : frameOperator (𝕜 := ℂ) (fun _ : Fin 2 => (1 : ℂ))
    = (2 : ℂ) • (1 : ℂ →L[ℂ] ℂ) := by
  have h := frameOperator_eq_smul_one_of_isTightFrame (𝕜 := ℂ) constFrame
  simpa using h

/-- The operator norm of the frame operator of the constant frame is at most `2`. -/
example : ‖frameOperator (𝕜 := ℂ) (fun _ : Fin 2 => (1 : ℂ))‖ ≤ 2 :=
  norm_frameOperator_le constFrame

/-- The inverse frame operator of the constant frame on `ℂ` is `(1 / 2) • 1`. -/
example : frameOperatorInv (𝕜 := ℂ) constFrame = ((1 / 2 : ℂ)) • (1 : ℂ →L[ℂ] ℂ) := by
  have hS : frameOperator (𝕜 := ℂ) (fun _ : Fin 2 => (1 : ℂ))
      = (2 : ℂ) • (1 : ℂ →L[ℂ] ℂ) := by
    have h := frameOperator_eq_smul_one_of_isTightFrame (𝕜 := ℂ) constFrame
    simpa using h
  have hcomp : frameOperator (𝕜 := ℂ) (fun _ : Fin 2 => (1 : ℂ))
      ∘L ((1 / 2 : ℂ) • (1 : ℂ →L[ℂ] ℂ)) = 1 := by
    rw [hS]
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply, smul_apply, one_apply_eq_self, smul_smul]
    rw [show (2 : ℂ) * (1 / 2) = 1 by norm_num, one_smul]
  calc frameOperatorInv (𝕜 := ℂ) constFrame
      = frameOperatorInv (𝕜 := ℂ) constFrame ∘L (1 : ℂ →L[ℂ] ℂ) := by
        rw [ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id]
    _ = frameOperatorInv (𝕜 := ℂ) constFrame ∘L (frameOperator (𝕜 := ℂ)
          (fun _ : Fin 2 => (1 : ℂ)) ∘L ((1 / 2 : ℂ) • (1 : ℂ →L[ℂ] ℂ))) := by
        rw [hcomp]
    _ = (frameOperatorInv (𝕜 := ℂ) constFrame ∘L frameOperator (𝕜 := ℂ)
          (fun _ : Fin 2 => (1 : ℂ))) ∘L ((1 / 2 : ℂ) • (1 : ℂ →L[ℂ] ℂ)) := by
        rw [ContinuousLinearMap.comp_assoc]
    _ = (1 : ℂ →L[ℂ] ℂ) ∘L ((1 / 2 : ℂ) • (1 : ℂ →L[ℂ] ℂ)) := by
        rw [frameOperatorInv_comp_frameOperator]
    _ = ((1 / 2 : ℂ)) • (1 : ℂ →L[ℂ] ℂ) := by
        rw [ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]

/-- The frame operator of the dual of the constant frame is the inverse
frame operator. -/
example : frameOperator (𝕜 := ℂ) (dualFrame constFrame)
    = frameOperatorInv (𝕜 := ℂ) constFrame :=
  frameOperator_dualFrame constFrame

/-- The dual of the constant frame on `ℂ` is a frame with bounds `1 / 2, 1 / 2`. -/
example : IsFrame (𝕜 := ℂ) (dualFrame constFrame) (1 / 2) (1 / 2) :=
  isFrame_dualFrame constFrame

/-- Reconstruction holds for the constant frame on `ℂ`. -/
example (x : ℂ) :
    ∑ _i : Fin 2, ⟪(1 : ℂ), frameOperatorInv (𝕜 := ℂ) constFrame x⟫_ℂ • (1 : ℂ) = x :=
  frame_reconstruction constFrame x

/-- An orthonormal basis is a frame with bounds `1, 1`. -/
example {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι 𝕜 E) :
    IsFrame (𝕜 := 𝕜) (fun i => b i) 1 1 := by
  refine ⟨by norm_num, by norm_num, fun x => ?_⟩
  rw [b.sum_sq_norm_inner_right x]
  constructor <;> simp

end MathlibExtTest.Analysis.InnerProductSpace.FiniteFrameTests
