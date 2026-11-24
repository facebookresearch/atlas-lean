/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Block solution equivalence by Schur elimination

For finite block matrices `A, B, C, D` over `Real` with `D` invertible,
the block equations `A *ᵥ x + B *ᵥ y = u` and `C *ᵥ x + D *ᵥ y = v` are
equivalent to the Schur-reduced equation
`(A - B * D⁻¹ * C) *ᵥ x = u - B *ᵥ (D⁻¹ *ᵥ v)` together with the
reconstruction `y = D⁻¹ *ᵥ (v - C *ᵥ x)`. The equivalence is packaged
once, as `elim_iff` with its two directions; no positivity, symmetry or
graph assumption is used. A nonzero interior right-hand side survives
reconstruction; singular `D` is excluded by the `Invertible D`
hypothesis.
-/

@[expose] public section

open Matrix

namespace MathlibExt.LinearAlgebra.Matrix.BlockSolutionEquiv

/-- The Schur complement of the invertible block `D`. -/
noncomputable def schur {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq p] (A : Matrix m n ℝ) (B : Matrix m p ℝ) (C : Matrix p n ℝ)
    (D : Matrix p p ℝ) [Invertible D] : Matrix m n ℝ :=
  A - B * D⁻¹ * C

/-- Forward elimination: a solution of the block system solves the
Schur-reduced equation and satisfies the reconstruction formula. -/
theorem elim_forward {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq p] {A : Matrix m n ℝ} {B : Matrix m p ℝ} {C : Matrix p n ℝ}
    {D : Matrix p p ℝ} [Invertible D] {x : n → ℝ} {y : p → ℝ} {u : m → ℝ}
    {v : p → ℝ} (h1 : A *ᵥ x + B *ᵥ y = u) (h2 : C *ᵥ x + D *ᵥ y = v) :
    schur A B C D *ᵥ x = u - B *ᵥ (D⁻¹ *ᵥ v)
      ∧ y = D⁻¹ *ᵥ (v - C *ᵥ x) := by
  have hD : ∀ w : p → ℝ, D⁻¹ *ᵥ (D *ᵥ w) = w := fun w => by
    rw [mulVec_mulVec, inv_mul_of_invertible, one_mulVec]
  have h2a : D⁻¹ *ᵥ (C *ᵥ x + D *ᵥ y) = D⁻¹ *ᵥ v := by rw [h2]
  rw [mulVec_add, hD] at h2a
  have hB : B *ᵥ (D⁻¹ *ᵥ (C *ᵥ x) + y) = B *ᵥ (D⁻¹ *ᵥ v) := by rw [h2a]
  rw [mulVec_add] at hB
  have hschur : schur A B C D *ᵥ x = A *ᵥ x - B *ᵥ (D⁻¹ *ᵥ (C *ᵥ x)) := by
    unfold schur
    rw [sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]
  constructor
  · rw [hschur]
    linear_combination h1 - hB
  · rw [mulVec_sub]
    linear_combination h2a

/-- Backward reconstruction: a solution of the Schur-reduced equation,
with `y` defined by the reconstruction formula, solves the block
system. -/
theorem elim_backward {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq p] {A : Matrix m n ℝ} {B : Matrix m p ℝ} {C : Matrix p n ℝ}
    {D : Matrix p p ℝ} [Invertible D] {x : n → ℝ} {u : m → ℝ} {v : p → ℝ}
    (h : schur A B C D *ᵥ x = u - B *ᵥ (D⁻¹ *ᵥ v)) :
    A *ᵥ x + B *ᵥ (D⁻¹ *ᵥ (v - C *ᵥ x)) = u
      ∧ C *ᵥ x + D *ᵥ (D⁻¹ *ᵥ (v - C *ᵥ x)) = v := by
  have hD' : ∀ w : p → ℝ, D *ᵥ (D⁻¹ *ᵥ w) = w := fun w => by
    rw [mulVec_mulVec, mul_inv_of_invertible, one_mulVec]
  have hschur : schur A B C D *ᵥ x = A *ᵥ x - B *ᵥ (D⁻¹ *ᵥ (C *ᵥ x)) := by
    unfold schur
    rw [sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]
  rw [hschur] at h
  have hBrec : B *ᵥ (D⁻¹ *ᵥ (v - C *ᵥ x))
      = B *ᵥ (D⁻¹ *ᵥ v) - B *ᵥ (D⁻¹ *ᵥ (C *ᵥ x)) := by
    rw [mulVec_sub, mulVec_sub]
  constructor
  · rw [hBrec]
    linear_combination h
  · rw [hD']
    abel

/-- The explicit solution correspondence: the block system holds for
`(x, y)` iff `x` solves the Schur-reduced equation and `y` is the
reconstruction `D⁻¹ *ᵥ (v - C *ᵥ x)`. -/
theorem elim_iff {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq p] {A : Matrix m n ℝ} {B : Matrix m p ℝ} {C : Matrix p n ℝ}
    {D : Matrix p p ℝ} [Invertible D] {x : n → ℝ} {y : p → ℝ} {u : m → ℝ}
    {v : p → ℝ} :
    (A *ᵥ x + B *ᵥ y = u ∧ C *ᵥ x + D *ᵥ y = v)
      ↔ (schur A B C D *ᵥ x = u - B *ᵥ (D⁻¹ *ᵥ v)
          ∧ y = D⁻¹ *ᵥ (v - C *ᵥ x)) := by
  constructor
  · rintro ⟨h1, h2⟩
    exact elim_forward h1 h2
  · rintro ⟨h, rfl⟩
    exact elim_backward h

end MathlibExt.LinearAlgebra.Matrix.BlockSolutionEquiv
