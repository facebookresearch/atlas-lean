/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Topology.Instances.Matrix

/-! # Jacobi's formula for a real matrix curve -/

@[expose] public section

open scoped Matrix.Norms.Elementwise

/-- **Jacobi's formula.** The derivative of the determinant of a differentiable square real
matrix curve is the trace of its adjugate times its derivative. The matrix need not be invertible.

Source: R. A. Horn and C. R. Johnson, *Matrix Analysis*, 2nd ed., §0.8.10.

See also `yalexey-jcode`'s earlier Lean proposal in
<https://github.com/leanprover-community/mathlib4/issues/41881>, which derives the Fréchet
derivative from the determinant's permutation expansion. This proof instead differentiates the
continuous multilinear determinant. -/
theorem Matrix.deriv_det_eq_trace_adjugate_mul {n : Type*} [Fintype n] [DecidableEq n]
    (A : ℝ → Matrix n n ℝ) (t : ℝ) (hA : DifferentiableAt ℝ A t) :
    deriv (fun s => (A s).det) t = Matrix.trace ((A t).adjugate * deriv A t) := by
  let d : ContinuousMultilinearMap ℝ (fun _ : n => n → ℝ) ℝ :=
    { toMultilinearMap := (Matrix.detRowAlternating : (n → ℝ) [⋀^n]→ₗ[ℝ] ℝ).toMultilinearMap
      cont := (continuous_id : Continuous (fun B : Matrix n n ℝ => B)).matrix_det }
  have hd : HasDerivAt (fun s => (A s).det) (d.linearDeriv (A t) (deriv A t)) t :=
    (d.hasFDerivAt (A t)).comp_hasDerivAt t hA.hasDerivAt
  calc
    deriv (fun s => (A s).det) t = d.linearDeriv (A t) (deriv A t) := hd.deriv
    _ = ∑ i, ((A t).updateRow i (deriv A t i)).det :=
      d.linearDeriv_apply (A t) (deriv A t)
    _ = _ := by
      rw [Matrix.trace_mul_comm (A t).adjugate (deriv A t)]
      simp_rw [← Matrix.cramer_transpose_apply, Matrix.cramer_eq_adjugate_mulVec,
        ← Matrix.adjugate_transpose, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
        Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, mul_comm]
