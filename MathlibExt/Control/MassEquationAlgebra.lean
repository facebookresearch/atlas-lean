/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Basic.Real.Basic

open scoped Matrix

/-!
# Pointwise mass-equation inversion

For a finite real mass matrix `M` with unit determinant, the
acceleration solving the mass equation `M *ᵥ a = F` is
`a = M⁻¹ *ᵥ F` (`mass_mulVec_eq_iff`), including the factored
force form `F = B *ᵥ τ - C *ᵥ v - g` with rectangular `B`
(`mass_mulVec_eq_iff_forces`). Pairing with `qdot = v` identifies
the first-order right-hand side `(v, M⁻¹ *ᵥ F)`
(`firstOrderRhs`, `eq_firstOrderRhs_iff`). This is the algebra
step only; deriving the mechanics equation is out of scope.
-/

@[expose] public section

namespace Control

/-- Pointwise mass-equation inversion: for a finite real mass
matrix `M` with unit determinant, the acceleration `a` solves
`M *ᵥ a = F` if and only if `a = M⁻¹ *ᵥ F`. This is the algebra
step only; it does not derive the mechanics equation. -/
theorem mass_mulVec_eq_iff {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (hM : IsUnit M.det) (F a : n → ℝ) :
    M *ᵥ a = F ↔ a = M⁻¹ *ᵥ F := by
  constructor
  · intro h
    calc a = (1 : Matrix n n ℝ) *ᵥ a := (Matrix.one_mulVec a).symm
      _ = (M⁻¹ * M) *ᵥ a := by rw [Matrix.nonsing_inv_mul M hM]
      _ = M⁻¹ *ᵥ (M *ᵥ a) := by rw [← Matrix.mulVec_mulVec]
      _ = M⁻¹ *ᵥ F := by rw [h]
  · intro h
    calc M *ᵥ a = M *ᵥ (M⁻¹ *ᵥ F) := by rw [h]
      _ = (M * M⁻¹) *ᵥ F := by rw [Matrix.mulVec_mulVec]
      _ = (1 : Matrix n n ℝ) *ᵥ F := by rw [Matrix.mul_nonsing_inv M hM]
      _ = F := Matrix.one_mulVec F

/-- The same inversion with the force in its standard factored
form `F = B *ᵥ τ - C *ᵥ v - g` (rectangular input matrix `B`
allowed): the acceleration is the inverse mass matrix applied to
the net force. -/
theorem mass_mulVec_eq_iff_forces {n m : Type*} [Fintype n]
    [DecidableEq n] [Fintype m] (M : Matrix n n ℝ) (hM : IsUnit M.det)
    (B : Matrix n m ℝ) (τ : m → ℝ) (C : Matrix n n ℝ) (v g a : n → ℝ) :
    M *ᵥ a = B *ᵥ τ - C *ᵥ v - g ↔
      a = M⁻¹ *ᵥ (B *ᵥ τ - C *ᵥ v - g) := by
  exact mass_mulVec_eq_iff M hM _ _

/-- The first-order right-hand side of the mass equation at
velocity `v` under net force `F`: the pair `(v, M⁻¹ *ᵥ F)` of
velocity and acceleration. -/
noncomputable def firstOrderRhs {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (F v : n → ℝ) : (n → ℝ) × (n → ℝ) :=
  (v, M⁻¹ *ᵥ F)

/-- A derivative pair `(x, y)` is the first-order right-hand side
if and only if the position derivative is the velocity and the
velocity derivative solves the mass equation. -/
theorem eq_firstOrderRhs_iff {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (hM : IsUnit M.det) (F v x y : n → ℝ) :
    (x, y) = firstOrderRhs M F v ↔ x = v ∧ M *ᵥ y = F := by
  unfold firstOrderRhs
  simp only [Prod.mk.injEq, mass_mulVec_eq_iff M hM F y]

end Control
