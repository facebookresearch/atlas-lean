/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

import MathlibExt.Analysis.InnerProductSpace.TensorProduct.InsideCompletion
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.NormNum

/-!
# Completing finite-support factors in a Hilbert tensor

The finitely supported sequences in complex ℓ² inherit the ambient inner
product. The left and right completion comparisons and their inverses
preserve the pure tensor formed with the nonreal vector i e₀. Its completed
tensor norm is one. A stock zero-dimensional Euclidean factor is included
on each side.
-/

noncomputable section

open UniformSpace
open scoped TensorProduct ENNReal

namespace MathlibExtTest.InsideCompletion

private abbrev ComplexL2 := lp (fun _ : ℕ => ℂ) 2
private def finiteSupportSubmodule : Submodule ℂ ComplexL2 :=
  Submodule.span ℂ (Set.range fun n : ℕ => lp.single (E := fun _ : ℕ => ℂ) 2 n 1)
private abbrev FiniteSupportL2 := finiteSupportSubmodule

private def unitVector : FiniteSupportL2 := by
  refine ⟨lp.single (E := fun _ : ℕ => ℂ) 2 0 1, ?_⟩
  exact Submodule.subset_span ⟨0, rfl⟩

private def phaseVector : FiniteSupportL2 := Complex.I • unitVector

private theorem norm_phaseVector : ‖phaseVector‖ = 1 := by
  change ‖Complex.I • (lp.single (E := fun _ : ℕ => ℂ) 2 0 1 : ComplexL2)‖ = 1
  rw [norm_smul, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
  simp

example :
    ‖((phaseVector ⊗ₜ[ℂ] (1 : ℂ) : FiniteSupportL2 ⊗[ℂ] ℂ) :
      Completion (FiniteSupportL2 ⊗[ℂ] ℂ))‖ = 1 := by
  rw [Completion.norm_coe, TensorProduct.norm_tmul, norm_phaseVector]
  simp

example :
    TensorProduct.completionLeftTensorEmbedding
        (𝕜 := ℂ) (E := FiniteSupportL2) (F := ℂ)
        (phaseVector ⊗ₜ[ℂ] (1 : ℂ) : Completion (FiniteSupportL2 ⊗[ℂ] ℂ)) =
      ↑((phaseVector : Completion FiniteSupportL2) ⊗ₜ[ℂ] (1 : ℂ) :
        (Completion FiniteSupportL2) ⊗[ℂ] ℂ) ∧
    TensorProduct.completionLeftTensorUnitary
        (𝕜 := ℂ) (E := FiniteSupportL2) (F := ℂ)
        (phaseVector ⊗ₜ[ℂ] (1 : ℂ) : Completion (FiniteSupportL2 ⊗[ℂ] ℂ)) =
      ↑((phaseVector : Completion FiniteSupportL2) ⊗ₜ[ℂ] (1 : ℂ) :
        (Completion FiniteSupportL2) ⊗[ℂ] ℂ) := by
  exact ⟨TensorProduct.completionLeftTensorEmbedding_tmul phaseVector (1 : ℂ),
    TensorProduct.completionLeftTensorUnitary_tmul phaseVector (1 : ℂ)⟩

example :
    (TensorProduct.completionLeftTensorUnitary
        (𝕜 := ℂ) (E := FiniteSupportL2) (F := ℂ)).symm
        ↑((phaseVector : Completion FiniteSupportL2) ⊗ₜ[ℂ] (1 : ℂ) :
          (Completion FiniteSupportL2) ⊗[ℂ] ℂ) =
      (phaseVector ⊗ₜ[ℂ] (1 : ℂ) : Completion (FiniteSupportL2 ⊗[ℂ] ℂ)) := by
  exact TensorProduct.completionLeftTensorUnitary_symm_tmul phaseVector (1 : ℂ)

example :
    TensorProduct.completionRightTensorEmbedding
        (𝕜 := ℂ) (E := ℂ) (F := FiniteSupportL2)
        ((1 : ℂ) ⊗ₜ[ℂ] phaseVector : Completion (ℂ ⊗[ℂ] FiniteSupportL2)) =
      ↑((1 : ℂ) ⊗ₜ[ℂ] (phaseVector : Completion FiniteSupportL2) :
        ℂ ⊗[ℂ] (Completion FiniteSupportL2)) ∧
    TensorProduct.completionRightTensorUnitary
        (𝕜 := ℂ) (E := ℂ) (F := FiniteSupportL2)
        ((1 : ℂ) ⊗ₜ[ℂ] phaseVector : Completion (ℂ ⊗[ℂ] FiniteSupportL2)) =
      ↑((1 : ℂ) ⊗ₜ[ℂ] (phaseVector : Completion FiniteSupportL2) :
        ℂ ⊗[ℂ] (Completion FiniteSupportL2)) := by
  exact ⟨TensorProduct.completionRightTensorEmbedding_tmul (1 : ℂ) phaseVector,
    TensorProduct.completionRightTensorUnitary_tmul (1 : ℂ) phaseVector⟩

example :
    (TensorProduct.completionRightTensorUnitary
        (𝕜 := ℂ) (E := ℂ) (F := FiniteSupportL2)).symm
        ↑((1 : ℂ) ⊗ₜ[ℂ] (phaseVector : Completion FiniteSupportL2) :
          ℂ ⊗[ℂ] (Completion FiniteSupportL2)) =
      ((1 : ℂ) ⊗ₜ[ℂ] phaseVector : Completion (ℂ ⊗[ℂ] FiniteSupportL2)) := by
  exact TensorProduct.completionRightTensorUnitary_symm_tmul (1 : ℂ) phaseVector

private abbrev ZeroHilbert := EuclideanSpace ℂ (Fin 0)

example :
    TensorProduct.completionLeftTensorUnitary
        (𝕜 := ℂ) (E := FiniteSupportL2) (F := ZeroHilbert)
        (phaseVector ⊗ₜ[ℂ] (0 : ZeroHilbert) :
          Completion (FiniteSupportL2 ⊗[ℂ] ZeroHilbert)) = 0 := by
  rw [TensorProduct.completionLeftTensorUnitary_tmul]
  simp

example :
    TensorProduct.completionRightTensorUnitary
        (𝕜 := ℂ) (E := ZeroHilbert) (F := FiniteSupportL2)
        ((0 : ZeroHilbert) ⊗ₜ[ℂ] phaseVector :
          Completion (ZeroHilbert ⊗[ℂ] FiniteSupportL2)) = 0 := by
  rw [TensorProduct.completionRightTensorUnitary_tmul]
  simp

end MathlibExtTest.InsideCompletion
