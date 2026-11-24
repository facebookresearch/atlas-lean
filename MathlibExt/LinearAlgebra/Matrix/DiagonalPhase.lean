/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Diagonal phase matrix

This module defines the diagonal unitary matrix whose diagonal entries are
`exp (θ i * I)` (equivalently `exp (I * θ i)`), i.e. `diagonal (fun i => cexp (θ i * I))`.
The definition is source-transparent, the matrix is unitary, and we expose both
the matrix and the bundled `unitaryGroup` element together with foundational laws:
entry description, star/conjugate-transpose as negation, addition as multiplication,
zero as one, unitary membership, and bundled unitary laws.

The sign convention is `exp (θ * I)`.

## Main definitions

* `Matrix.diagonalPhase` – the diagonal phase matrix.
* `Matrix.diagonalPhaseU` – the same as a `unitaryGroup` element.

## Main results

* `diagonalPhase_apply` – entry description.
* `diagonalPhase_conjTranspose_eq_neg` / `diagonalPhase_neg` – conjugate transpose is negation.
* `diagonalPhase_add` / `diagonalPhase_zero` – multiplication laws.
* `diagonalPhase_mem_unitary` – unitary membership.
* `diagonalPhaseU` laws: `val`, `mul`, `zero`, `inv`.
-/

@[expose] public section

open Matrix Complex ComplexConjugate

namespace Matrix

variable {n : Type*} [DecidableEq n]

/-- Diagonal phase matrix: `diagonal (fun i => exp (θ i * I))`.
Transparent: unfolds directly to `diagonal`. Preserves the exact `exp (θ * I)` convention. -/
noncomputable def diagonalPhase (θ : n → ℝ) : Matrix n n ℂ :=
  diagonal (fun i => Complex.exp ((θ i : ℂ) * Complex.I))

private theorem star_exp_eq (z : ℂ) : star (Complex.exp z) = Complex.exp (star z) := by
  calc star (Complex.exp z) = conj (Complex.exp z) := rfl
    _ = Complex.exp (conj z) := by rw [← Complex.exp_conj]
    _ = Complex.exp (star z) := rfl

private theorem star_mul_I_ofReal (r : ℝ) :
    star ((r : ℂ) * Complex.I) = -((r : ℂ) * Complex.I) := by
  apply Complex.ext
  · simp [mul_re, ofReal_re, ofReal_im, I_re, I_im]
  · simp [mul_im, ofReal_re, ofReal_im, I_re, I_im]

omit [DecidableEq n] in
private theorem diagonalPhase_star_entry (θ : n → ℝ) (i : n) :
    star (Complex.exp ((θ i : ℂ) * Complex.I)) =
      Complex.exp (-((θ i : ℂ) * Complex.I)) := by
  rw [star_exp_eq, star_mul_I_ofReal]

private theorem diagonalPhase_mul_conjTranspose [Fintype n] (θ : n → ℝ) :
    diagonalPhase θ * (diagonalPhase θ)ᴴ = 1 := by
  unfold diagonalPhase
  rw [diagonal_conjTranspose, diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp only [diagonal_apply_eq, one_apply_eq]
    have h_mul : Complex.exp ((θ i : ℂ) * Complex.I) *
        star (Complex.exp ((θ i : ℂ) * Complex.I)) = 1 := by
      rw [diagonalPhase_star_entry, ← Complex.exp_add]
      have : ((θ i : ℂ) * Complex.I) + -((θ i : ℂ) * Complex.I) = 0 := by ring
      rw [this, Complex.exp_zero]
    exact h_mul
  · simp only [diagonal_apply_ne _ hij, one_apply_ne hij]

private theorem diagonalPhase_conjTranspose_mul [Fintype n] (θ : n → ℝ) :
    (diagonalPhase θ)ᴴ * diagonalPhase θ = 1 := by
  unfold diagonalPhase
  rw [diagonal_conjTranspose, diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp only [diagonal_apply_eq, one_apply_eq]
    have h_mul : star (Complex.exp ((θ i : ℂ) * Complex.I)) *
        Complex.exp ((θ i : ℂ) * Complex.I) = 1 := by
      rw [diagonalPhase_star_entry, ← Complex.exp_add]
      have : -((θ i : ℂ) * Complex.I) + ((θ i : ℂ) * Complex.I) = 0 := by ring
      rw [this, Complex.exp_zero]
    exact h_mul
  · simp only [diagonal_apply_ne _ hij, one_apply_ne hij]

/-- Entry description for the diagonal phase matrix. -/
theorem diagonalPhase_apply (θ : n → ℝ) (i j : n) :
    diagonalPhase θ i j =
      if i = j then Complex.exp ((θ i : ℂ) * Complex.I) else 0 := by
  unfold diagonalPhase
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij]

/-- Zero angles give the identity matrix. -/
theorem diagonalPhase_zero :
    diagonalPhase (n := n) (fun _ => (0 : ℝ)) = 1 := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [diagonalPhase]
  · simp [diagonalPhase, hij]

/-- Addition of angles corresponds to multiplication of diagonal phase matrices. -/
theorem diagonalPhase_add [Fintype n] (θ₁ θ₂ : n → ℝ) :
    diagonalPhase (fun i => θ₁ i + θ₂ i) =
      diagonalPhase θ₁ * diagonalPhase θ₂ := by
  unfold diagonalPhase
  rw [diagonal_mul_diagonal]
  congr 1
  funext i
  have h : ((θ₁ i + θ₂ i : ℝ) : ℂ) * Complex.I =
      ((θ₁ i : ℂ) * Complex.I) + ((θ₂ i : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_add]

/-- Negation of angles corresponds to conjugate transpose. -/
theorem diagonalPhase_neg (θ : n → ℝ) :
    diagonalPhase (fun i => -θ i) = (diagonalPhase θ)ᴴ := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp only [diagonalPhase, diagonal_apply_eq, diagonal_conjTranspose,
      diagonal_apply_eq, Pi.star_apply]
    have h1 : ((-θ i : ℝ) : ℂ) * Complex.I =
        -((θ i : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [h1, ← diagonalPhase_star_entry]
  · have hij' : j ≠ i := Ne.symm hij
    simp [diagonalPhase_apply, hij, hij', conjTranspose_apply]

/-- Conjugate transpose equals diagonal phase with negated angles. -/
theorem diagonalPhase_conjTranspose_eq_neg (θ : n → ℝ) :
    (diagonalPhase θ)ᴴ = diagonalPhase (fun i => -θ i) :=
  (diagonalPhase_neg θ).symm

/-- Diagonal phase matrices are unitary. -/
theorem diagonalPhase_mem_unitary [Fintype n] (θ : n → ℝ) :
    diagonalPhase θ ∈ unitaryGroup n ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  exact diagonalPhase_mul_conjTranspose θ

/-- Diagonal phase as a unitary-group element. -/
noncomputable def diagonalPhaseU [Fintype n] (θ : n → ℝ) : unitaryGroup n ℂ :=
  ⟨diagonalPhase θ, diagonalPhase_mem_unitary θ⟩

@[simp]
theorem diagonalPhaseU_val [Fintype n] (θ : n → ℝ) :
    (diagonalPhaseU θ : Matrix n n ℂ) = diagonalPhase θ :=
  rfl

theorem diagonalPhaseU_mul [Fintype n] (θ₁ θ₂ : n → ℝ) :
    diagonalPhaseU (fun i => θ₁ i + θ₂ i) =
      diagonalPhaseU θ₁ * diagonalPhaseU θ₂ := by
  apply Subtype.ext
  exact diagonalPhase_add θ₁ θ₂

theorem diagonalPhaseU_zero [Fintype n] :
    diagonalPhaseU (n := n) (fun _ => (0 : ℝ)) = 1 := by
  apply Subtype.ext
  exact diagonalPhase_zero

theorem diagonalPhaseU_inv [Fintype n] (θ : n → ℝ) :
    (diagonalPhaseU θ)⁻¹ = diagonalPhaseU (fun i => -θ i) := by
  apply Subtype.ext
  calc (↑(diagonalPhaseU θ)⁻¹ : Matrix n n ℂ) = star (diagonalPhase θ) := rfl
    _ = (diagonalPhase θ)ᴴ := rfl
    _ = diagonalPhase (fun i => -θ i) := (diagonalPhase_neg θ).symm

end Matrix
