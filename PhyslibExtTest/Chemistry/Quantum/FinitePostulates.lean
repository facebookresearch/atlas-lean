/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Chemistry.Quantum.FinitePostulates
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Finite-dimensional quantum postulate checks

Concrete consumers of `PhyslibExt.Chemistry.Quantum.FinitePostulates`: the Pauli matrices,
Pauli time evolution, Pauli-`X` eigenvectors, the trace argument, and a simultaneous
diagonalization. The spectral decomposition check uses Mathlib's canonical spectral theorem.

## i. Overview

These are elaboration and exact-computation checks, not new results. The Pauli matrices are
`σx = !![0, 1; 1, 0]`, `σy = !![0, -I; I, 0]`, and `σz = !![1, 0; 0, -1]` over `ℂ`.
Born-probability checks are in `PhyslibExtTest.Quantum.FiniteState`, using the canonical
`Quantum.FiniteState` API. This file makes no uncertainty-inequality claim.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Pauli matrices
- B. Pauli time evolution
- C. Pauli-`X` eigenvectors
- D. Trace argument
- E. Simultaneous diagonalization

## iv. References

- `PhyslibExt.Chemistry.Quantum.FinitePostulates`
- `Matrix.IsHermitian.spectral_theorem`

## A. Pauli matrices
-/

open scoped Matrix

local notation "σx" => (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ)
local notation "σy" => (!![0, -Complex.I; Complex.I, 0] : Matrix (Fin 2) (Fin 2) ℂ)
local notation "σz" => (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ)

/-- `σx` is Hermitian. -/
example : Matrix.IsHermitian σx :=
  Matrix.IsHermitian.ext fun i j => by fin_cases i <;> fin_cases j <;> simp

/-- `σz` is Hermitian. -/
example : Matrix.IsHermitian σz :=
  Matrix.IsHermitian.ext fun i j => by fin_cases i <;> fin_cases j <;> simp

/-- `σy` is Hermitian. -/
example : Matrix.IsHermitian σy :=
  Matrix.IsHermitian.ext fun i j => by fin_cases i <;> fin_cases j <;> simp

/-- The commutator `[σx, σz] = σx * σz - σz * σx` is `-2 i σy`, with the scalar `-2 * I`. -/
example : σx * σz - σz * σx = (-2 * Complex.I) • σy := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [mul_assoc]

/-- The same identity in the literal form `-2 * Complex.I • σy`, which Lean parses as the
matrix product `(-2 : Matrix (Fin 2) (Fin 2) ℂ) * (Complex.I • σy)`. -/
example : σx * σz - σz * σx = -2 * Complex.I • σy := by
  rw [neg_mul, two_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

/-! ## B. Pauli time evolution -/

/-- `exp (-(t / ħ) • (I • σz))` is unitary for every real `t` and `ħ ≠ 0`, by
`unitary_time_evolution`. -/
example (t ħ : ℝ) (hħ : ħ ≠ 0) :
    NormedSpace.exp (-(t / ħ) • (Complex.I • σz)) ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  Chemistry.Quantum.unitary_time_evolution _
    (Matrix.IsHermitian.ext fun i j => by fin_cases i <;> fin_cases j <;> simp) t ħ hħ

/-- At `t = π * ħ / 2`, Mathlib's `Matrix.exp_diagonal` gives the diagonal matrix with entries
`exp (-(I * π / 2))` and `exp (I * π / 2)`, that is `!![-I, 0; 0, I]`. -/
example (ħ : ℝ) (hħ : ħ ≠ 0) :
    NormedSpace.exp (-((Real.pi * ħ / 2) / ħ) • (Complex.I • σz)) =
        Matrix.diagonal
          ![Complex.exp (-(Complex.I * Real.pi / 2)), Complex.exp (Complex.I * Real.pi / 2)] ∧
      NormedSpace.exp (-((Real.pi * ħ / 2) / ħ) • (Complex.I • σz)) =
        !![-Complex.I, 0; 0, Complex.I] := by
  have hdiag : NormedSpace.exp (-((Real.pi * ħ / 2) / ħ) • (Complex.I • σz)) =
      Matrix.diagonal
        ![Complex.exp (-(Complex.I * Real.pi / 2)), Complex.exp (Complex.I * Real.pi / 2)] := by
    have hθ : (Real.pi * ħ / 2) / ħ = Real.pi / 2 := by field_simp
    have hσz : σz = Matrix.diagonal ![1, -1] := by
      rw [Matrix.diagonal_fin_two]
      rfl
    have hvec : -(Real.pi / 2) • Complex.I • ![(1 : ℂ), -1] =
        ![-(Complex.I * Real.pi / 2), Complex.I * Real.pi / 2] := by
      ext i
      fin_cases i <;> simp [Complex.real_smul] <;> ring
    rw [hθ, hσz, ← Matrix.diagonal_smul, ← Matrix.diagonal_smul, Matrix.exp_diagonal, hvec]
    congr 1
    funext i
    rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]
    fin_cases i <;> rfl
  refine ⟨hdiag, ?_⟩
  have hneg : Complex.exp (-(Complex.I * Real.pi / 2)) = -Complex.I := by
    rw [show -(Complex.I * Real.pi / 2) = -Real.pi / 2 * Complex.I by ring]
    exact Complex.exp_neg_pi_div_two_mul_I
  have hpos : Complex.exp (Complex.I * Real.pi / 2) = Complex.I := by
    rw [show Complex.I * Real.pi / 2 = Real.pi / 2 * Complex.I by ring]
    exact Complex.exp_pi_div_two_mul_I
  rw [hdiag, hneg, hpos, Matrix.diagonal_fin_two]
  rfl

/-! ## C. Pauli-`X` eigenvectors -/

/-- `![1, 1]` is an eigenvector of `σx` with eigenvalue `1`. -/
example : σx *ᵥ ![1, 1] = (1 : ℂ) • ![1, 1] := by
  ext i
  fin_cases i <;> simp

/-- `![1, -1]` is an eigenvector of `σx` with eigenvalue `-1`. -/
example : σx *ᵥ ![1, -1] = (-1 : ℂ) • ![1, -1] := by
  ext i
  fin_cases i <;> simp

/-- The two eigenvectors of `σx` are orthogonal. -/
example : star (![1, 1] : Fin 2 → ℂ) ⬝ᵥ ![1, -1] = 0 := by
  simp [dotProduct]

/-- Mathlib's spectral theorem decomposes `σx` using a unitary eigenbasis and real eigenvalues. -/
example :
    ∃ U ∈ Matrix.unitaryGroup (Fin 2) ℂ, ∃ d : Fin 2 → ℝ,
      σx = U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ := by
  have hX : Matrix.IsHermitian σx :=
    Matrix.IsHermitian.ext fun i j => by fin_cases i <;> fin_cases j <;> simp
  refine ⟨hX.eigenvectorUnitary, hX.eigenvectorUnitary.2, hX.eigenvalues, ?_⟩
  refine hX.spectral_theorem.trans ?_
  rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
  rfl

/-! ## D. Trace argument -/

/-- The trace of the commutator `[σx, σz]` vanishes. -/
example : Matrix.trace (σx * σz - σz * σx) = 0 := by
  simp [Matrix.trace_fin_two]

/-- The trace of `(I * ħ) • 1` on `ℂ²` is `2 * I * ħ`, which is nonzero for `ħ ≠ 0`. -/
example (ħ : ℝ) (hħ : ħ ≠ 0) :
    Matrix.trace ((Complex.I * (ħ : ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) =
        2 * Complex.I * ħ ∧
      (2 * Complex.I * ħ : ℂ) ≠ 0 := by
  refine ⟨?_, by simp [hħ]⟩
  rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
  push_cast
  ring

/-- `no_finite_dim_canonical_commutator` on `ℂ²`: no `X`, `P` satisfy `[X, P] = I • ħ • 1`. -/
example (ħ : ℝ) (hħ : ħ ≠ 0) :
    ¬ ∃ X P : Matrix (Fin 2) (Fin 2) ℂ, X * P - P * X = Complex.I • (ħ : ℂ) • 1 :=
  fun ⟨X, P, h⟩ => Chemistry.Quantum.no_finite_dim_canonical_commutator two_pos ħ hħ X P h

/-! ## E. Simultaneous diagonalization -/

/-- `simultaneous_orthonormal_eigenbasis` applies to the commuting, non-diagonal Hermitian pair
`σx` and `!![2, 1; 1, 2]`. -/
example :
    ∃ U ∈ Matrix.unitaryGroup (Fin 2) ℂ, ∃ a b : Fin 2 → ℝ,
      Uᴴ * σx * U = Matrix.diagonal (fun i => (a i : ℂ)) ∧
        Uᴴ * !![2, 1; 1, 2] * U = Matrix.diagonal (fun i => (b i : ℂ)) :=
  Chemistry.Quantum.simultaneous_orthonormal_eigenbasis _ _
    (Matrix.IsHermitian.ext fun i j => by fin_cases i <;> fin_cases j <;> simp)
    (Matrix.IsHermitian.ext fun i j => by fin_cases i <;> fin_cases j <;> simp)
    (by
      change σx * !![2, 1; 1, 2] = !![2, 1; 1, 2] * σx
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num)
