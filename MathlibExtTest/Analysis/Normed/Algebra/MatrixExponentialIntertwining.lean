/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Normed.Algebra.MatrixExponentialIntertwining

/-!
# Tests for intertwining and the matrix exponential

A rectangular intertwiner between a `2 × 2` and a `1 × 1` matrix (a common eigenvector), the
square case `X = 1`, and the summed form used for row sums of rate matrices.
-/

@[expose] public section

namespace MathlibExtTest.Analysis.Normed.Algebra.MatrixExponentialIntertwining

open Matrix

/-- An eigenvector as a `2 × 1` intertwiner: if `A v = a v` then `exp A v = e^a v`. -/
example (A : Matrix (Fin 2) (Fin 2) ℝ) (v : Matrix (Fin 2) (Fin 1) ℝ) (a : ℝ)
    (h : A * v = v * Matrix.of ![![a]]) :
    NormedSpace.exp A * v = v * NormedSpace.exp (Matrix.of ![![a]]) :=
  exp_mul_eq_mul_exp_of_mul_eq h

/-- The square case `X = 1` is trivial: `exp A * 1 = 1 * exp A`. -/
example (A : Matrix (Fin 3) (Fin 3) ℂ) : NormedSpace.exp A * 1 = 1 * NormedSpace.exp A :=
  exp_mul_eq_mul_exp_of_mul_eq (by rw [Matrix.mul_one, Matrix.one_mul])

/-- A matrix with zero row sums has `exp` with unit row sums (the all-ones column intertwines it
with the `1 × 1` zero matrix). -/
example (Q : Matrix (Fin 2) (Fin 2) ℝ) (hQ : ∀ i, ∑ j, Q i j = 0) (i : Fin 2) :
    ∑ j, NormedSpace.exp Q i j = 1 := by
  let X : Matrix (Fin 2) (Fin 1) ℝ := Matrix.of fun _ _ => 1
  have hX : Q * X = X * (0 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext i j
    simp [X, Matrix.mul_apply, hQ]
  have h := congrFun (congrFun (exp_mul_eq_mul_exp_of_mul_eq hX) i) 0
  rw [NormedSpace.exp_zero, Matrix.mul_one] at h
  simpa [Matrix.mul_apply, X] using h

end MathlibExtTest.Analysis.Normed.Algebra.MatrixExponentialIntertwining
