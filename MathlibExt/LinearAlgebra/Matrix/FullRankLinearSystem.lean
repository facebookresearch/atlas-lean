/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Full-rank square linear systems have a unique solution

A square real linear system `A *ᵥ x = b` whose coefficient matrix has
injective `mulVec` (the full-rank certificate) has exactly one solution,
and when `det A` is a unit that solution is the explicit vector
`A⁻¹ *ᵥ b`. The second theorem is the usable form: `A *ᵥ x = b` holds
exactly when `x = A⁻¹ *ᵥ b`, so the inverse vector both solves the system
and certifies that no other vector does.

## i. Overview

Injectivity of `mulVec` is equivalent to `IsUnit A`
(`Matrix.mulVec_injective_iff_isUnit`), and a unit matrix has surjective
`mulVec` (`Matrix.mulVec_surjective_iff_isUnit`), which gives existence;
injectivity itself gives uniqueness. For the explicit form, multiplying by
`A⁻¹` and using `Matrix.nonsing_inv_mul` / `Matrix.mul_nonsing_inv`
reduces both directions to `1 *ᵥ x = x`.

## ii. Key results

- `Matrix.exists_unique_mulVec_eq`: a full-rank square system has exactly
  one solution.
- `Matrix.mulVec_eq_iff_inv_mulVec`: with `IsUnit A.det`, `A *ᵥ x = b`
  exactly when `x = A⁻¹ *ᵥ b`.

## iii. Table of contents

- A. Existence and uniqueness from injective `mulVec`
- B. Explicit solution from a unit determinant

## iv. References

- `Matrix.mulVec_injective_iff_isUnit`,
  `Matrix.mulVec_surjective_iff_isUnit`, `Matrix.nonsing_inv_mul`,
  `Matrix.mul_nonsing_inv` (Mathlib).
-/

@[expose] public section

namespace Matrix

/-! ## A. Existence and uniqueness from injective `mulVec` -/

/-- A full-rank (injective `mulVec`) square system has exactly one solution. -/
theorem exists_unique_mulVec_eq {n : Type*} [Fintype n]
    {A : Matrix n n ℝ} (hinj : Function.Injective A.mulVec) (b : n → ℝ) :
    ∃! x : n → ℝ, A *ᵥ x = b := by
  classical
  have hUnit : IsUnit A := Matrix.mulVec_injective_iff_isUnit.mp hinj
  have hsurj : Function.Surjective A.mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr hUnit
  obtain ⟨x0, hx0⟩ := hsurj b
  exact ⟨x0, hx0, fun y hy => hinj (hy.trans hx0.symm)⟩

/-! ## B. Explicit solution from a unit determinant -/

/-- With a unit determinant, the solution is explicit: `x = A⁻¹ *ᵥ b` is the
unique solution, so `A⁻¹ *ᵥ b` is both a solver and the uniqueness certificate. -/
theorem mulVec_eq_iff_inv_mulVec {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : IsUnit A.det) {b x : n → ℝ} :
    A *ᵥ x = b ↔ x = A⁻¹ *ᵥ b := by
  constructor
  · intro h
    have h1 : A⁻¹ *ᵥ (A *ᵥ x) = A⁻¹ *ᵥ b := by rw [h]
    rw [mulVec_mulVec, nonsing_inv_mul _ hA, one_mulVec] at h1
    exact h1
  · intro h
    rw [h, mulVec_mulVec, mul_nonsing_inv _ hA, one_mulVec]

end Matrix
