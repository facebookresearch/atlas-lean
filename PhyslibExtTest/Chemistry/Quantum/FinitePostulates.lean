/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Chemistry.Quantum.FinitePostulates
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Real.Sqrt
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

Concrete consumers of `PhyslibExt.Chemistry.Quantum.FinitePostulates`: a two-state Born rule,
the Pauli matrices, a Robertson-inequality instance, Pauli time evolution, Pauli-`X`
eigenvectors, the trace argument, and a simultaneous diagonalization.

## i. Overview

These are elaboration and exact-computation checks, not new results. The Pauli matrices are
`σx = !![0, 1; 1, 0]`, `σy = !![0, -I; I, 0]`, and `σz = !![1, 0; 0, -1]` over `ℂ`.

The Robertson check in section C uses this variance convention. For a unit state `ψ` and an
observable `A`, the expectation is `⟪A ψ, ψ⟫ = star (A *ᵥ ψ) ⬝ᵥ ψ`, and the variance is the
centred squared Euclidean norm `∑ i, ‖(A *ᵥ ψ - ⟪A ψ, ψ⟫ • ψ) i‖ ^ 2`. For Hermitian `A`
the expectation is real, and the agreement of this variance with MathlibExt's
`RobertsonUncertainty.variance` on unit states is a mathematical identification under the
Euclidean-space representation (coordinate vectors as elements of `EuclideanSpace ℂ (Fin 2)`,
the coordinate sum as the squared norm, and the dot product as the inner product); this file
and `PhyslibExt.Chemistry.Quantum.FinitePostulates` do not prove that conversion. The check is
an instance test for `σx`, `σz` in `ψ = ![1, 0]`, and it is degenerate: the variances of `σx`
and `σz` are `1` and `0` and the commutator expectation is `0`, so the checked inequality reads
`1 * 0 ≥ 0`; it exercises neither a nonzero uncertainty bound nor the general Robertson theorem.
The state is retained because the contract pinned it. The general Robertson inequality is
`MathlibExt.Analysis.InnerProductSpace.RobertsonUncertainty.robertson`; it is not re-proved.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Born rule for a two-state superposition
- B. Pauli matrices
- C. Robertson inequality for `σx`, `σz`
- D. Pauli time evolution
- E. Pauli-`X` eigenvectors
- F. Trace argument
- G. Simultaneous diagonalization

## iv. References

- `PhyslibExt.Chemistry.Quantum.FinitePostulates`
- `MathlibExt.Analysis.InnerProductSpace.RobertsonUncertainty`

## A. Born rule for a two-state superposition
-/

open scoped Matrix

local notation "σx" => (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ)
local notation "σy" => (!![0, -Complex.I; Complex.I, 0] : Matrix (Fin 2) (Fin 2) ℂ)
local notation "σz" => (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ)
local notation "ψ₊" => (![1 / Real.sqrt 2, 1 / Real.sqrt 2] : Fin 2 → ℂ)
local notation "ψ₀" => (![1, 0] : Fin 2 → ℂ)

/-- `ψ₊ = ![1 / √2, 1 / √2]` is a unit vector. -/
example : star ψ₊ ⬝ᵥ ψ₊ = 1 := by
  have h : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt zero_le_two]
    norm_num
  norm_num [dotProduct, Fin.sum_univ_two, h]

/-- In the computational basis (`U = 1`), both Born probabilities of `ψ₊` are `1 / 2`. -/
example :
    ‖((1 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ *ᵥ ψ₊) 0‖ ^ 2 = 1 / 2 ∧
      ‖((1 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ *ᵥ ψ₊) 1‖ ^ 2 = 1 / 2 := by
  simp

/-- The two Born probabilities of `ψ₊` sum to `1`, by `born_probabilities_sum_eq_one`. -/
example : ∑ i, ‖((1 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ *ᵥ ψ₊) i‖ ^ 2 = 1 :=
  Chemistry.Quantum.born_probabilities_sum_eq_one 1 (one_mem _) _ (by
    have h : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 := by
      rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt zero_le_two]
      norm_num
    norm_num [dotProduct, Fin.sum_univ_two, h])

/-! ## B. Pauli matrices -/

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

/-! ## C. Robertson inequality for `σx`, `σz` -/

/-- `ψ₀ = ![1, 0]` is a unit vector. -/
example : star ψ₀ ⬝ᵥ ψ₀ = 1 := by
  simp [dotProduct]

/-- Variance of `σx` in `ψ₀`: the expectation `⟪σx ψ₀, ψ₀⟫` is `0`, and the centred
squared norm is `1`. -/
example :
    star (σx *ᵥ ψ₀) ⬝ᵥ ψ₀ = 0 ∧
      ∑ i, ‖(σx *ᵥ ψ₀ - (star (σx *ᵥ ψ₀) ⬝ᵥ ψ₀) • ψ₀) i‖ ^ 2 = 1 := by
  simp [dotProduct, Fin.sum_univ_two]

/-- Variance of `σz` in `ψ₀`: the expectation `⟪σz ψ₀, ψ₀⟫` is `1`, and the centred
squared norm is `0`, since `ψ₀` is an eigenvector of `σz`. -/
example :
    star (σz *ᵥ ψ₀) ⬝ᵥ ψ₀ = 1 ∧
      ∑ i, ‖(σz *ᵥ ψ₀ - (star (σz *ᵥ ψ₀) ⬝ᵥ ψ₀) • ψ₀) i‖ ^ 2 = 0 := by
  simp [dotProduct, Fin.sum_univ_two]

/-- The commutator expectation `⟪[σx, σz] ψ₀, ψ₀⟫` is `0`. -/
example : star ((σx * σz - σz * σx) *ᵥ ψ₀) ⬝ᵥ ψ₀ = 0 := by
  simp [dotProduct, Fin.sum_univ_two]

/-- Robertson inequality instance:
`Var(σx) * Var(σz) ≥ (1 / 4) * ‖⟪[σx, σz] ψ₀, ψ₀⟫‖ ^ 2`, here `1 * 0 ≥ 0`. -/
example :
    (1 / 4 : ℝ) * ‖star ((σx * σz - σz * σx) *ᵥ ψ₀) ⬝ᵥ ψ₀‖ ^ 2 ≤
      (∑ i, ‖(σx *ᵥ ψ₀ - (star (σx *ᵥ ψ₀) ⬝ᵥ ψ₀) • ψ₀) i‖ ^ 2) *
        ∑ i, ‖(σz *ᵥ ψ₀ - (star (σz *ᵥ ψ₀) ⬝ᵥ ψ₀) • ψ₀) i‖ ^ 2 := by
  simp [dotProduct, Fin.sum_univ_two]

/-! ## D. Pauli time evolution -/

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

/-! ## E. Pauli-`X` eigenvectors -/

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

/-- `spectral_orthonormal_eigenbasis` applies to `σx`. -/
example :
    ∃ U ∈ Matrix.unitaryGroup (Fin 2) ℂ, ∃ d : Fin 2 → ℝ,
      Uᴴ * σx * U = Matrix.diagonal (fun i => (d i : ℂ)) :=
  Chemistry.Quantum.spectral_orthonormal_eigenbasis _
    (Matrix.IsHermitian.ext fun i j => by fin_cases i <;> fin_cases j <;> simp)

/-! ## F. Trace argument -/

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

/-! ## G. Simultaneous diagonalization -/

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
