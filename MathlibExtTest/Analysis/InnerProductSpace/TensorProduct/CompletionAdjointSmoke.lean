/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.InnerProductSpace.TensorProduct.CompletionAdjoint
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.NormNum

/-! # Completed adjoints between four distinct stock Euclidean spaces -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open UniformSpace
open scoped TensorProduct

namespace CompletedTensorAdjointSmoke

-- All four factors have their stock finite-dimensional complete Hilbert-space instances.
private abbrev E₁ := EuclideanSpace ℂ (Fin 1)
private abbrev E₂ := EuclideanSpace ℂ (Fin 2)
private abbrev F₁ := EuclideanSpace ℂ (Fin 3)
private abbrev F₂ := EuclideanSpace ℂ (Fin 4)
private abbrev SourceTensor := Completion (E₁ ⊗[ℂ] F₁)
private abbrev TargetTensor := Completion (E₂ ⊗[ℂ] F₂)

private def a : E₁ := EuclideanSpace.single 0 (1 : ℂ)
private def b : E₂ := EuclideanSpace.single 1 (1 : ℂ)
private def c : F₁ := EuclideanSpace.single 2 (1 : ℂ)
private def d : F₂ := EuclideanSpace.single 3 (1 : ℂ)
private def sourceUnit : SourceTensor := (a ⊗ₜ[ℂ] c : SourceTensor)
private def targetUnit : TargetTensor := (b ⊗ₜ[ℂ] d : TargetTensor)

-- The rectangular maps have nonreal coefficients; the adjoints reverse their types.
private def f : E₁ →L[ℂ] E₂ := InnerProductSpace.rankOne ℂ ((1 + Complex.I) • b) a
private def g : F₁ →L[ℂ] F₂ := InnerProductSpace.rankOne ℂ ((2 + Complex.I) • d) c

private theorem f_a : f a = (1 + Complex.I) • b := by
  simp [f, a, InnerProductSpace.rankOne_apply]

private theorem g_c : g c = (2 + Complex.I) • d := by
  simp [g, c, InnerProductSpace.rankOne_apply]

private theorem adjoint_f_b : f.adjoint b = star (1 + Complex.I) • a := by
  unfold f
  rw [InnerProductSpace.adjoint_rankOne, InnerProductSpace.rankOne_apply, inner_smul_left]
  simp [b]

private theorem adjoint_g_d : g.adjoint d = star (2 + Complex.I) • c := by
  unfold g
  rw [InnerProductSpace.adjoint_rankOne, InnerProductSpace.rankOne_apply, inner_smul_left]
  simp [d, RCLike.conj_ofNat]

private theorem adjoint_coefficient :
    star (1 + Complex.I) * star (2 + Complex.I) = (1 - 3 * Complex.I : ℂ) := by
  apply Complex.ext <;> norm_num [Complex.mul_re, Complex.mul_im]

private theorem sourceUnit_inner_self : inner ℂ sourceUnit sourceUnit = 1 := by
  unfold sourceUnit
  rw [Completion.inner_coe, TensorProduct.inner_tmul]
  simp [a, c]

private theorem sourceUnit_ne_zero : sourceUnit ≠ 0 := by
  intro h
  have hi := sourceUnit_inner_self
  rw [h, inner_zero_left] at hi
  norm_num at hi

private theorem completed_adjoint_value :
    (TensorProduct.mapLCompletion f g).adjoint targetUnit =
      (1 - 3 * Complex.I) • sourceUnit := by
  rw [TensorProduct.adjoint_mapLCompletion]
  unfold targetUnit sourceUnit
  rw [TensorProduct.mapLCompletion_tmul, adjoint_f_b, adjoint_g_d]
  change
    ((star (1 + Complex.I) • a) ⊗ₜ[ℂ] (star (2 + Complex.I) • c) : SourceTensor) =
      (1 - 3 * Complex.I) • ((a ⊗ₜ[ℂ] c : E₁ ⊗[ℂ] F₁) : SourceTensor)
  rw [TensorProduct.smul_tmul_smul, Completion.coe_smul, adjoint_coefficient]

-- Both operators visibly have nonreal matrix entries in the canonical coordinates.
example : (f a) 1 = 1 + Complex.I ∧ (g c) 3 = 2 + Complex.I := by
  rw [f_a, g_c]
  simp [b, d]

-- This evaluates the public completed-adjoint theorem on a genuine nonzero pure tensor.
example :
    (TensorProduct.mapLCompletion f g).adjoint targetUnit =
      (1 - 3 * Complex.I) • sourceUnit ∧ sourceUnit ≠ 0 :=
  ⟨completed_adjoint_value, sourceUnit_ne_zero⟩

example :
    inner ℂ sourceUnit ((TensorProduct.mapLCompletion f g).adjoint targetUnit) =
      1 - 3 * Complex.I := by
  rw [completed_adjoint_value, inner_smul_right, sourceUnit_inner_self, mul_one]

end CompletedTensorAdjointSmoke
