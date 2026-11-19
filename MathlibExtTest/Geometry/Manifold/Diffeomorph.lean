/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.Manifold.Diffeomorph

/-!
# Group laws for self-diffeomorphisms of the plane

Tests for the `Group (M ≃ₘ^n⟮I, I⟯ M)` instance on two noncommuting
diffeomorphisms of `ℝ × ℝ`: doubling of the first coordinate and swap.
-/

@[expose] public section

open scoped Manifold ContDiff

noncomputable section

namespace DiffeomorphGroupTests

/-- The plane, with the sup norm. -/
abbrev P := ℝ × ℝ

/-- Doubling of the first coordinate. -/
def D : P ≃ₘ^∞⟮𝓘(ℝ, P), 𝓘(ℝ, P)⟯ P :=
  ((LinearEquiv.smulOfNeZero ℝ ℝ 2 (by norm_num)).toContinuousLinearEquiv.prodCongr
    (ContinuousLinearEquiv.refl ℝ ℝ)).toDiffeomorph

/-- Coordinate swap. -/
def S : P ≃ₘ^∞⟮𝓘(ℝ, P), 𝓘(ℝ, P)⟯ P :=
  (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ).toDiffeomorph

/-- Application formula for `D`. -/
theorem D_apply (x y : ℝ) : D (x, y) = (2 * x, y) := by
  unfold D
  simp only [ContinuousLinearEquiv.coe_toDiffeomorph,
    ContinuousLinearEquiv.prodCongr_apply,
    LinearEquiv.coe_toContinuousLinearEquiv',
    LinearEquiv.smulOfNeZero_apply, ContinuousLinearEquiv.refl_apply,
    smul_eq_mul]

/-- Application formula for `S`. -/
theorem S_apply (x y : ℝ) : S (x, y) = (y, x) := by
  unfold S
  simp only [ContinuousLinearEquiv.coe_toDiffeomorph,
    ContinuousLinearEquiv.prodComm_apply]
  rfl

/-- Pin: `D` doubles the first coordinate of `(1, 0)`. -/
theorem D_pin : D (1, 0) = (2, 0) := by
  rw [D_apply, mul_one]

/-- Pin: `S` swaps `(1, 0)`. -/
theorem S_pin : S (1, 0) = (0, 1) :=
  S_apply 1 0

/-- Composition order: first `D`, then `S`. -/
theorem comp_SD :
    (S * D) (1, 0) = (0, 2) := by
  rw [Diffeomorph.mul_apply, D_pin]
  exact S_apply 2 0

/-- Composition order: first `S`, then `D`. -/
theorem comp_DS :
    (D * S) (1, 0) = (0, 1) := by
  rw [Diffeomorph.mul_apply, S_pin, D_apply, mul_zero]

/-- The diffeomorphism group is not commutative. -/
theorem mul_ne :
    S * D ≠ D * S := by
  intro h
  have h1 : (S * D) (1, 0) = (0, 2) := comp_SD
  have h2 : (D * S) (1, 0) = (0, 1) := comp_DS
  rw [h] at h1
  rw [h2] at h1
  have hS : (1 : ℝ) = 2 := congrArg Prod.snd h1
  exact (by norm_num : (1 : ℝ) ≠ 2) hS

/-- The identity acts as the identity. -/
theorem one_pin :
    (1 : P ≃ₘ^∞⟮𝓘(ℝ, P), 𝓘(ℝ, P)⟯ P) (3, 4) = (3, 4) :=
  Diffeomorph.one_apply _

/-- The inverse of `D` halves the first coordinate. -/
theorem invD_pin : D⁻¹ (2, 0) = (1, 0) := by
  rw [← D_pin, Diffeomorph.inv_apply]
  exact Diffeomorph.symm_apply_apply D (1, 0)

/-- The swap is an involution. -/
theorem SS_one : S * S = 1 := by
  apply Diffeomorph.ext
  intro x
  obtain ⟨a, b⟩ := x
  simp [Diffeomorph.mul_apply, Diffeomorph.one_apply, S_apply]

/-- The inverse of the swap is itself. -/
theorem Sinv_eq : S⁻¹ = S := by
  have h1 : S * S = 1 := SS_one
  have h2 : S * S⁻¹ = 1 := mul_inv_cancel S
  rw [← h1] at h2
  exact mul_left_cancel h2

/-- The group law `D⁻¹ * D = 1` on a point. -/
theorem inv_mul_point :
    (D⁻¹ * D) (5, 7) = (5, 7) := by
  rw [inv_mul_cancel]
  exact Diffeomorph.one_apply _

end DiffeomorphGroupTests

end
