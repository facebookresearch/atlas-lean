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

public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Trace norm of finite complex matrices

For a square complex matrix on any finite index type, the trace norm is the
sum of the singular values of its associated Euclidean linear map. The sum
is over natural indices `0,...,card(n)-1`, which contains every possibly
nonzero singular value. This is the Schatten-one quantity, with the original
Euclidean coordinate structure.

The trace norm is nonnegative and is zero exactly for the zero matrix. An
empty index type gives the empty sum and value zero. No Hermitian, positive-
semidefinite, trace-one or invertibility hypothesis is used.
-/

@[expose] public section

open Matrix LinearMap Finset Module

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Trace norm of a finite square complex matrix, defined as the sum of
singular values of its associated linear map `Matrix.toEuclideanLin`.
We sum over `Finset.range (Fintype.card n)`, which contains all possibly
nonzero singular values for an `n × n` matrix.

Here `n` is any finite index type with decidable equality. The matrices are arbitrary square
complex matrices, and the empty-index case is included. -/
noncomputable def singularValueTraceNorm (M : Matrix n n ℂ) : ℝ :=
  ∑ i ∈ Finset.range (Fintype.card n),
    (Matrix.toEuclideanLin M).singularValues i

/-- The matrix trace norm is exactly the finite sum of its Euclidean linear map singular values
over indices below the matrix dimension.

Here `n` is any finite index type with decidable equality. The matrices are arbitrary square
complex matrices, and the empty-index case is included.

```lean
theorem singularValueTraceNorm_eq_sum (M : Matrix n n ℂ) :
    M.singularValueTraceNorm = ∑ i ∈ Finset.range (Fintype.card n),
      (Matrix.toEuclideanLin M).singularValues i
``` -/
@[simp]
theorem singularValueTraceNorm_eq_sum (M : Matrix n n ℂ) :
    M.singularValueTraceNorm = ∑ i ∈ Finset.range (Fintype.card n),
      (Matrix.toEuclideanLin M).singularValues i := rfl

/-- The finite complex matrix trace norm is nonnegative.

Here `n` is any finite index type with decidable equality. The matrices are arbitrary square
complex matrices, and the empty-index case is included.

```lean
theorem singularValueTraceNorm_nonneg (M : Matrix n n ℂ) : 0 ≤ M.singularValueTraceNorm
``` -/
theorem singularValueTraceNorm_nonneg (M : Matrix n n ℂ) : 0 ≤ M.singularValueTraceNorm := by
  unfold singularValueTraceNorm
  apply Finset.sum_nonneg
  intro i _
  exact (Matrix.toEuclideanLin M).singularValues_nonneg i

/-- The zero matrix has trace norm zero.

Here `n` is any finite index type with decidable equality. The matrices are arbitrary square
complex matrices, and the empty-index case is included.

```lean
theorem singularValueTraceNorm_zero : (0 : Matrix n n ℂ).singularValueTraceNorm = 0
``` -/
@[simp]
theorem singularValueTraceNorm_zero : (0 : Matrix n n ℂ).singularValueTraceNorm = 0 := by
  unfold singularValueTraceNorm
  simp

/-- A finite complex matrix has trace norm zero exactly when it is the zero matrix.

Here `n` is any finite index type with decidable equality. The matrices are arbitrary square
complex matrices, and the empty-index case is included.

```lean
theorem singularValueTraceNorm_eq_zero_iff (M : Matrix n n ℂ) :
    M.singularValueTraceNorm = 0 ↔ M = 0
``` -/
theorem singularValueTraceNorm_eq_zero_iff (M : Matrix n n ℂ) :
    M.singularValueTraceNorm = 0 ↔ M = 0 := by
  constructor
  · intro h
    unfold singularValueTraceNorm at h
    have h_nonneg : ∀ i ∈ Finset.range (Fintype.card n),
        0 ≤ (Matrix.toEuclideanLin M).singularValues i := fun i _ =>
      (Matrix.toEuclideanLin M).singularValues_nonneg i
    have h_sum_zero :=
      (Finset.sum_eq_zero_iff_of_nonneg h_nonneg).mp h
    have h_sv_zero : ∀ i, (Matrix.toEuclideanLin M).singularValues i = 0 := by
      intro i
      by_cases hi : i < Fintype.card n
      · have := h_sum_zero i (Finset.mem_range.mpr hi)
        exact this
      · have h_le : Fintype.card n ≤ i := Nat.le_of_not_lt hi
        have h_finrank :
            finrank ℂ (EuclideanSpace ℂ n) = Fintype.card n := by
          simp [finrank_euclideanSpace]
        rw [← h_finrank] at h_le
        exact (Matrix.toEuclideanLin M).singularValues_of_finrank_le h_le
    have h_sv : (Matrix.toEuclideanLin M).singularValues = 0 := by
      ext i
      exact h_sv_zero i
    have h_lin : Matrix.toEuclideanLin M = 0 := by
      rw [LinearMap.singularValues_eq_zero_iff] at h_sv
      exact h_sv
    have h_eq : M = 0 := by
      apply (Matrix.toEuclideanLin : Matrix n n ℂ ≃ₗ[ℂ] _).injective
      simp [h_lin]
    exact h_eq
  · rintro rfl
    exact singularValueTraceNorm_zero

end Matrix
