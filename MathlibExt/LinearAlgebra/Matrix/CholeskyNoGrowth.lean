/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Matrix.Mul

/-!
# No element growth in Cholesky factorization

If `A = L Lᵀ` with `L` real, then by the Cauchy–Schwarz inequality
`(|L| |Lᵀ|)ᵢⱼ = ∑ₖ |Lᵢₖ| |Lⱼₖ| ≤ √(Aᵢᵢ) √(Aⱼⱼ) ≤ maxₖ Aₖₖ`. In the backward error bound
`|E| ≤ c n ε |L| |Lᵀ|` for Cholesky factorization, the factor `|L| |Lᵀ|` is therefore bounded by
the largest diagonal entry of `A`: Cholesky needs no pivoting to be backward stable
(J. W. Demmel, Math 221, UC Berkeley, Lecture 6 notes of 1 October 2024, error analysis of
Cholesky).
-/

@[expose] public section

namespace MathlibExt.LinearAlgebra.Matrix.CholeskyNoGrowth

open Finset

/-- **No element growth in Cholesky factorization.** If `A = L Lᵀ` for a real `n × n` matrix `L`,
then `∑ₖ |L(i, k)| |L(j, k)| ≤ √(A(i, i)) √(A(j, j))` for all `i, j` (Demmel, Math 221 Lecture 6
notes, 2024: "`(|L|*|L|^T)_{ij} <= norm(L(i,:))*norm(L(j,:)) = sqrt(A_{ii})*sqrt(A_{jj})`"). -/
theorem sum_abs_mul_abs_le_sqrt_mul_sqrt {n : Type*} [Fintype n] (L A : Matrix n n ℝ)
    (hA : A = L * L.transpose) (i j : n) :
    ∑ k, |L i k| * |L j k| ≤ √(A i i) * √(A j j) := by
  have hii : A i i = ∑ k, |L i k| ^ 2 := by
    rw [hA, Matrix.mul_apply]; simp [sq]
  have hjj : A j j = ∑ k, |L j k| ^ 2 := by
    rw [hA, Matrix.mul_apply]; simp [sq]
  rw [hii, hjj]
  exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _

/-- **No element growth, max form.** Under `A = L Lᵀ`, every entry of `|L| |Lᵀ|` is at most any
common bound `c` on the diagonal entries of `A`. -/
theorem sum_abs_mul_abs_le_of_diag_le {n : Type*} [Fintype n] (L A : Matrix n n ℝ)
    (hA : A = L * L.transpose) {c : ℝ} (hc : ∀ k, A k k ≤ c) (i j : n) :
    ∑ k, |L i k| * |L j k| ≤ c := by
  have hnn : ∀ k, 0 ≤ A k k := fun k => by
    rw [hA, Matrix.mul_apply]
    exact sum_nonneg fun _ _ => by simpa [Matrix.transpose_apply] using mul_self_nonneg (L k _)
  refine (sum_abs_mul_abs_le_sqrt_mul_sqrt L A hA i j).trans ?_
  calc √(A i i) * √(A j j) ≤ √c * √c := by gcongr <;> exact hc _
    _ = c := Real.mul_self_sqrt ((hnn i).trans (hc i))

end MathlibExt.LinearAlgebra.Matrix.CholeskyNoGrowth
