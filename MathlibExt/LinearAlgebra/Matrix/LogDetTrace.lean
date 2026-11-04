/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The log-determinant trace inequality

`Matrix.PosDef.log_det_mul_le_trace`: for real positive definite matrices `A` and `B`,
`log (det A * det B) ≤ tr (A B) - n`, where `n` is the dimension. The eigenvalues `λ` of the
positive definite matrix `√B A √B` (whose determinant is `det A det B` and whose trace is
`tr (A B)`) satisfy `log λ ≤ λ - 1`.

With `B` a sample covariance and `A` a candidate precision matrix, this is the inequality behind
the closed-form maximum likelihood covariance of Gaussian models: `A ↦ log det A - tr (A B)` is
maximized at `A = B⁻¹`.
-/

@[expose] public section

namespace Matrix.PosDef

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped MatrixOrder in
/-- **Log-determinant trace inequality.** Let $A$ and $B$ be positive definite real square
matrices indexed by a finite set with $n$ elements. Then
$\log(\det A \cdot \det B) \le \operatorname{tr}(AB) - n$.

The eigenvalues $\lambda$ of the positive definite matrix $B^{1/2} A B^{1/2}$, where $B^{1/2}$ is
the positive semidefinite square root of $B$, satisfy $\log \lambda \le \lambda - 1$; this
matrix has determinant $\det A \det B$ and trace $\operatorname{tr}(AB)$. -/
theorem log_det_mul_le_trace {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef) :
    log (A.det * B.det) ≤ (A * B).trace - Fintype.card ι := by
  set R := CFC.sqrt B
  have hR : R.PosSemidef := nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg B)
  have hRR : R * R = B := CFC.sqrt_mul_sqrt_self B (nonneg_iff_posSemidef.2 hB.posSemidef)
  have hdetR : R.det * R.det = B.det := by rw [← det_mul, hRR]
  have hRdet : R.det ≠ 0 := fun h => by
    have := hB.det_pos
    rw [← hdetR, h, zero_mul] at this
    exact lt_irrefl _ this
  have hinj : Function.Injective R.mulVec := fun u v huv => by
    have h := congrArg (R⁻¹ *ᵥ ·) huv
    simpa [mulVec_mulVec, nonsing_inv_mul R (isUnit_iff_ne_zero.2 hRdet)] using h
  have hM : (Rᴴ * A * R).PosDef := hA.conjTranspose_mul_mul_same hinj
  rw [hR.1] at hM
  have hdet : (R * A * R).det = A.det * B.det := by
    rw [det_mul, det_mul, ← hdetR]
    ring
  have htr : (R * A * R).trace = (A * B).trace := by
    rw [trace_mul_cycle, ← hRR, ← Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]
  rw [← hdet, ← htr, hM.1.det_eq_prod_eigenvalues, hM.1.trace_eq_sum_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id, id]
  rw [log_prod fun i _ => (hM.eigenvalues_pos i).ne']
  calc ∑ i, log (hM.1.eigenvalues i) ≤ ∑ i, (hM.1.eigenvalues i - 1) :=
        sum_le_sum fun i _ => log_le_sub_one_of_pos (hM.eigenvalues_pos i)
    _ = _ := by
        rw [sum_sub_distrib]
        simp

end Matrix.PosDef
