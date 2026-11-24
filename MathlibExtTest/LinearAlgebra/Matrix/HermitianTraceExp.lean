/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.HermitianTraceExp

@[expose] public section

open Matrix
open scoped ComplexOrder

namespace MathlibExtTest.LinearAlgebra.Matrix.HermitianTraceExp

/-- The trace exponential of the zero matrix is the dimension. -/
example (θ : ℝ) :
    RCLike.re (NormedSpace.exp (θ • (0 : Matrix (Fin 3) (Fin 3) ℂ))).trace = 3 := by
  rw [(isHermitian_zero).re_trace_exp_smul_eq_sum θ]
  have h : ∀ i, (isHermitian_zero (n := Fin 3) (α := ℂ)).eigenvalues i = 0 := by
    intro i
    have := (isHermitian_zero (n := Fin 3) (α := ℂ)).eigenvalues_eq i
    simpa using this
  simp [h]

/-- `λmin ≤ λmax` for any nonempty Hermitian matrix, a sanity check of the definitions. -/
example (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.IsHermitian) : hA.lambdaMin ≤ hA.lambdaMax :=
  hA.lambdaMin_le_lambdaMax

/-- The trace dominates each eigenvalue of a positive-semidefinite matrix. -/
example (A : Matrix (Fin 3) (Fin 3) ℂ) (hA : A.PosSemidef) (i : Fin 3) :
    hA.1.eigenvalues i ≤ RCLike.re A.trace :=
  hA.eigenvalues_le_re_trace i

-- `diag(1, -1)` is Hermitian.
theorem isHermitian_diag_one_neg_one : (diagonal ![(1 : ℂ), -1]).IsHermitian := by
  rw [isHermitian_diagonal_iff]
  intro i
  fin_cases i <;> simp [IsSelfAdjoint]

/-- The trace-exponential API on a non-scalar matrix: for `A = diag(1, -1)`, `tr e^{θA}` is the
sum of `e^{θλᵢ}` over its eigenvalues, `e^{θλmax} ≤ tr e^{θA}`, and `e^{θA}` is the standard
matrix function of `e^{θ·}`. -/
example (θ : ℝ) :
    (NormedSpace.exp (θ • diagonal ![(1 : ℂ), -1])).trace =
        ∑ i, (Real.exp (θ * isHermitian_diag_one_neg_one.eigenvalues i) : ℂ) ∧
      Real.exp (θ * isHermitian_diag_one_neg_one.lambdaMax) ≤
        RCLike.re (NormedSpace.exp (θ • diagonal ![(1 : ℂ), -1])).trace ∧
      NormedSpace.exp (θ • diagonal ![(1 : ℂ), -1]) =
        cfc (fun x => Real.exp (θ * x)) (diagonal ![(1 : ℂ), -1]) :=
  ⟨isHermitian_diag_one_neg_one.trace_exp_smul_eq_sum θ,
    isHermitian_diag_one_neg_one.exp_mul_lambdaMax_le_re_trace_exp θ,
    isHermitian_diag_one_neg_one.exp_smul_eq_cfc θ⟩

end MathlibExtTest.LinearAlgebra.Matrix.HermitianTraceExp
