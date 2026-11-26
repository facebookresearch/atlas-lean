/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Algebra.Homology.Hochschild.HomologyZero
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Focused clients for degree-zero Hochschild homology

The coefficients are the algebra `A` of `2 × 2` rational matrices acting on itself,
on the left by multiplication and on the right through `Aᵐᵒᵖ`; these actions are
not symmetric.

* The nonzero commutator `E₁₂ = E₁₁ E₁₂ - E₁₂ E₁₁` has zero class in `HH₀`.
* The trace kills every commutator, descends through `HH₀`, and sends the class of
  `E₁₁` to `1`, so that class is nonzero.
* The boundary of `E₁₂ ⊗ E₁₁` is `E₁₂ E₁₁ - E₁₁ E₁₂ = -E₁₂`; swapping the two actions
  would give `E₁₂`.
* For the commutative algebra `ℚ[X]` acting on itself the boundary vanishes and
  `HH₀` is the coefficient module.
-/

open ModuleCat.Algebra.Hochschild
open scoped TensorProduct

namespace MathlibExtTest.Algebra.Homology.Hochschild

/-- The rational `2 × 2` matrix algebra. -/
abbrev A := Matrix (Fin 2) (Fin 2) ℚ

/-- The matrix unit `E₁₁`. -/
abbrev E₁₁ : A := Matrix.single 0 0 1

/-- The matrix unit `E₁₂`. -/
abbrev E₁₂ : A := Matrix.single 0 1 1

lemma E₁₁_mul_E₁₂ : E₁₁ * E₁₂ = E₁₂ := by
  simp [Matrix.single_mul_single_same]

lemma E₁₂_mul_E₁₁ : E₁₂ * E₁₁ = 0 := by
  simp [Matrix.single_mul_single_of_ne]

lemma E₁₂_ne_zero : E₁₂ ≠ 0 := by
  intro h
  have := congrFun (congrFun h 0) 1
  simp at this

/-- The commutator `E₁₁ • E₁₂ - E₁₂ • E₁₁` is `E₁₂`. -/
lemma commutator_E₁₁_E₁₂ : E₁₁ • E₁₂ - MulOpposite.op E₁₁ • E₁₂ = E₁₂ := by
  rw [smul_eq_mul, op_smul_eq_mul, E₁₁_mul_E₁₂, E₁₂_mul_E₁₁, sub_zero]

/-- A nonzero commutator has zero class in `HH₀`. -/
example : E₁₂ ≠ 0 ∧ zeroClassMap ℚ A A E₁₂ = 0 := by
  refine ⟨E₁₂_ne_zero, (zeroClassMap_eq_zero_iff ℚ A A E₁₂).2 ?_⟩
  rw [← commutator_E₁₁_E₁₂]
  exact commutator_mem ℚ A A E₁₁ E₁₂

/-- The trace kills every commutator `a • m - m • a`. -/
lemma trace_commutator (a m : A) :
    Matrix.traceLinearMap (Fin 2) ℚ ℚ (a • m - MulOpposite.op a • m) = 0 := by
  rw [smul_eq_mul, op_smul_eq_mul, map_sub, Matrix.traceLinearMap_apply,
    Matrix.traceLinearMap_apply, Matrix.trace_mul_comm, sub_self]

/-- The trace through degree-zero Hochschild homology. -/
noncomputable def traceHH₀ : (homology ℚ A A 0).carrier →ₗ[ℚ] ℚ :=
  descZero ℚ A A (Matrix.traceLinearMap (Fin 2) ℚ ℚ) trace_commutator

/-- The trace detects the class of `E₁₁`. -/
lemma traceHH₀_E₁₁ : traceHH₀ (zeroClassMap ℚ A A E₁₁) = 1 := by
  rw [traceHH₀, descZero_zeroClassMap, Matrix.traceLinearMap_apply]
  simp [Matrix.trace_single_eq_same]

/-- The class of `E₁₁` in `HH₀` is nonzero, so `E₁₁` is not a sum of commutators. -/
example : zeroClassMap ℚ A A E₁₁ ≠ 0 ∧ E₁₁ ∉ commutatorSubmodule ℚ A A := by
  have h : zeroClassMap ℚ A A E₁₁ ≠ 0 := by
    intro h0
    have := traceHH₀_E₁₁
    rw [h0, map_zero] at this
    exact zero_ne_one this
  exact ⟨h, fun hm => h ((zeroClassMap_eq_zero_iff ℚ A A E₁₁).2 hm)⟩

/-- The degree-one boundary is `m ⊗ a ↦ m a - a m`; on `E₁₂ ⊗ E₁₁` it is `-E₁₂`. -/
lemma boundary_E₁₂_E₁₁ : boundaryLinearMap ℚ A A (E₁₂ ⊗ₜ[ℚ] E₁₁) = -E₁₂ := by
  rw [boundaryLinearMap_tmul, op_smul_eq_mul, smul_eq_mul, E₁₂_mul_E₁₁,
    E₁₁_mul_E₁₂, zero_sub]

/-- The sign is detected: the action-swapped value `E₁₂` is different. -/
example : boundaryLinearMap ℚ A A (E₁₂ ⊗ₜ[ℚ] E₁₁) ≠ E₁₂ := by
  rw [boundary_E₁₂_E₁₁]
  intro h
  have := congrFun (congrFun h 0) 1
  norm_num at this

/-- The boundary lands in the commutator submodule. -/
example : boundaryLinearMap ℚ A A (E₁₂ ⊗ₜ[ℚ] E₁₁) ∈ commutatorSubmodule ℚ A A := by
  rw [← range_boundaryLinearMap]
  exact LinearMap.mem_range_self _ _

section Symmetric

/-- For the commutative algebra `ℚ[X]` the two actions agree. -/
lemma polynomial_actions_symm (a m : Polynomial ℚ) : a • m = MulOpposite.op a • m := by
  rw [smul_eq_mul, op_smul_eq_mul, mul_comm]

/-- Symmetric case: the boundary vanishes on every generator. -/
example (m a : Polynomial ℚ) :
    boundaryLinearMap ℚ (Polynomial ℚ) (Polynomial ℚ) (m ⊗ₜ[ℚ] a) = 0 := by
  rw [boundaryLinearMap_tmul, ← polynomial_actions_symm, sub_self]

/-- Symmetric case: `HH₀(ℚ[X], ℚ[X])` is `ℚ[X]`, and the class of `X` is nonzero. -/
example : zeroClassMap ℚ (Polynomial ℚ) (Polynomial ℚ) Polynomial.X ≠ 0 := by
  intro h
  have := congrArg
    (homologyZeroSymmetricEquiv ℚ (Polynomial ℚ) (Polynomial ℚ) polynomial_actions_symm) h
  rw [homologyZeroSymmetricEquiv_zeroClassMap, map_zero] at this
  exact Polynomial.X_ne_zero this

end Symmetric

end MathlibExtTest.Algebra.Homology.Hochschild
