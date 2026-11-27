/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.RingTheory.PhiNModule.Basic
import Mathlib.Algebra.Module.Prod
import Mathlib.LinearAlgebra.Prod

/-! # Tests for `(φ, N)`-modules

The defining relation, stable subspaces, the restriction and quotient structures, kernels and
images of morphisms, and a concrete two-dimensional `(φ, N)`-module over `ℚ` (with `σ = id` and
`p = 2`): `φ (a, b) = (a, 2 b)` and `N (a, b) = (b, 0)`, with the stable line `ℚ × 0`.
-/

open Module

namespace MathlibExtTest.RingTheory.PhiNModule.Basic

section General

variable {K₀ : Type*} [Field K₀] {σ σ' : K₀ →+* K₀} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
  {p : K₀} {D : Type*} [AddCommGroup D] [Module K₀ D] (M : PhiNModule σ p D)

example (x : D) : M.N (M.φ x) = p • M.φ (M.N x) := M.N_φ x

example (c : K₀) (x : D) : M.φ (c • x) = σ c • M.φ x := M.φ.map_smulₛₗ c x

example : M.IsStable ⊥ := PhiNModule.isStable_bot

example : M.IsStable ⊤ := PhiNModule.isStable_top

example (φ : D ≃ₛₗ[σ] D) (x : D) : (PhiNModule.ofPhi (p := p) φ).N x = 0 := by simp

variable [FiniteDimensional K₀ D] {D' : Submodule K₀ D} (h : M.IsStable D')

example (x : D') : ((M.restrict D' h).φ x : D) = M.φ x := by simp

example (x : D') : ((M.restrict D' h).N x : D) = M.N x := by simp

example (x : D) :
    (M.quotient D' h).φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (M.φ x) := by simp

/-- `φ` maps a stable subspace of a finite-dimensional `(φ, N)`-module onto itself. -/
example : D'.map (M.φ : D →ₛₗ[σ] D) = D' := h.map_φ_eq

example {x : D} (hx : M.φ x ∈ D') : x ∈ D' := h.mem_of_φ_mem hx

variable {D₂ : Type*} [AddCommGroup D₂] [Module K₀ D₂] {M₂ : PhiNModule σ p D₂} (f : M.Hom M₂)

example : M.IsStable (LinearMap.ker f.toLinearMap) := f.isStable_ker

example : M₂.IsStable (LinearMap.range f.toLinearMap) := f.isStable_range

end General

section Concrete

/-- The Frobenius `φ (a, b) = (a, 2 b)` on `ℚ × ℚ`. -/
noncomputable def φ₀ : (ℚ × ℚ) ≃ₗ[ℚ] (ℚ × ℚ) :=
  (LinearEquiv.refl ℚ ℚ).prodCongr (LinearEquiv.smulOfNeZero ℚ ℚ 2 two_ne_zero)

/-- The monodromy `N (a, b) = (b, 0)` on `ℚ × ℚ`. -/
def N₀ : (ℚ × ℚ) →ₗ[ℚ] (ℚ × ℚ) := LinearMap.inl ℚ ℚ ℚ ∘ₗ LinearMap.snd ℚ ℚ ℚ

/-- A two-dimensional `(φ, N)`-module over `ℚ`, with `σ = id`, `p = 2` and `N ≠ 0`. -/
noncomputable def M₀ : PhiNModule (RingHom.id ℚ) (2 : ℚ) (ℚ × ℚ) where
  φ := φ₀
  N := N₀
  N_φ x := by
    obtain ⟨a, b⟩ := x
    simp [φ₀, N₀]

/-- The line `ℚ × 0` is stable under `φ` and `N`. -/
theorem isStable_range_inl : M₀.IsStable (LinearMap.range (LinearMap.inl ℚ ℚ ℚ)) where
  φ_mem := by
    rintro - ⟨a, rfl⟩
    exact ⟨a, by simp [M₀, φ₀]⟩
  N_mem := by
    rintro - ⟨a, rfl⟩
    exact ⟨0, by simp [M₀, N₀]⟩

example : M₀.N ≠ 0 := by
  intro h
  have := congrArg (fun f => f ((0 : ℚ), (1 : ℚ))) h
  simp [M₀, N₀] at this

/-- The quotient by the stable line is the one-dimensional `φ`-module with `φ = 2` and `N = 0`. -/
example (b : ℚ) :
    (M₀.quotient _ isStable_range_inl).N (Submodule.Quotient.mk ((0 : ℚ), b)) = 0 := by
  rw [PhiNModule.quotient_N_mk, Submodule.Quotient.mk_eq_zero]
  exact ⟨b, by simp [M₀, N₀]⟩

end Concrete

end MathlibExtTest.RingTheory.PhiNModule.Basic
