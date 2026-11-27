/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.LinearAlgebra.Determinant.Semilinear
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Basis.Defs

/-! # Tests for determinants of semilinear maps in a basis

For complex conjugation on `ℂ`, a semilinear map along `σ = conj`, the determinant in the basis
`(1)` is `1` and in the basis `(i)` it is `σ i / i = -1`: unlike for linear maps, it depends on the
basis, as `Module.Basis.det_mul_det_compₛₗ` predicts.
-/

open Module

namespace MathlibExtTest.LinearAlgebra.Determinant.Semilinear

section General

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {σ : R →+* R}
  {ι : Type*} [Fintype ι] [DecidableEq ι]

example (b : Basis ι R M) (f : M →ₛₗ[σ] M) (v : ι → M) :
    b.det (f ∘ v) = b.det (f ∘ b) * σ (b.det v) :=
  b.det_compₛₗ f v

/-- For a linear map, `det_compₛₗ` recovers `Module.Basis.det_comp`. -/
example (b : Basis ι R M) (f : M →ₗ[R] M) (v : ι → M) :
    b.det (f ∘ v) = b.det (f ∘ b) * b.det v :=
  b.det_compₛₗ f v

end General

/-- Complex conjugation, as a semilinear equivalence of `ℂ` along `starRingEnd ℂ`. -/
noncomputable abbrev conj : ℂ ≃ₛₗ[starRingEnd ℂ] ℂ := starLinearEquiv ℂ

/-- The standard basis `(1)` of `ℂ`. -/
noncomputable abbrev b₀ : Basis (Fin 1) ℂ ℂ := Basis.singleton (Fin 1) ℂ

/-- The basis `(i)` of `ℂ`. -/
noncomputable abbrev b₁ : Basis (Fin 1) ℂ ℂ :=
  b₀.unitsSMul fun _ => Units.mk0 Complex.I Complex.I_ne_zero

example : IsUnit (b₁.det (conj ∘ b₁)) := b₁.isUnit_det_compₛₗ conj

theorem det_b₀ : b₀.det ((conj : ℂ →ₛₗ[starRingEnd ℂ] ℂ) ∘ b₀) = 1 := by
  simp [Basis.det_apply, Matrix.det_unique, Basis.toMatrix_apply]

theorem det_b₀_b₁ : b₀.det b₁ = Complex.I := by
  simp [Basis.det_apply, Matrix.det_unique]

/-- In the basis `(i)` the determinant of conjugation is `-1`. -/
example : b₁.det ((conj : ℂ →ₛₗ[starRingEnd ℂ] ℂ) ∘ b₁) = -1 := by
  have h := b₀.det_mul_det_compₛₗ b₁ (conj : ℂ →ₛₗ[starRingEnd ℂ] ℂ)
  rw [det_b₀, det_b₀_b₁, one_mul, Complex.conj_I] at h
  exact mul_left_cancel₀ Complex.I_ne_zero (h.trans (by ring))

end MathlibExtTest.LinearAlgebra.Determinant.Semilinear
