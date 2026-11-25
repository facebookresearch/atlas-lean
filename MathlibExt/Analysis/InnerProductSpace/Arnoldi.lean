/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.LinearAlgebra.Matrix.Hessenberg.Defs

/-!
# The Arnoldi and Lanczos iterations: Hessenberg and tridiagonal structure

Let `T` be a linear operator on an inner product space `E` over `𝕜 = ℝ` or `ℂ`, and `r ∈ E`.
The Krylov vectors are `r, T r, …, T^{k-1} r`. The Arnoldi iteration is the (modified)
Gram–Schmidt process applied to this Krylov sequence (Trefethen and Bau, *Numerical Linear
Algebra*, Lecture 33): in exact arithmetic and without breakdown, i.e. when the Krylov vectors
are linearly independent, the Arnoldi vectors are the normalized Gram–Schmidt vectors
`q_0, …, q_{k-1}` of the Krylov vectors (`arnoldiVec`). The coefficients
`h_ij = ⟪q_i, T q_j⟫` form the matrix `H_k = Q_kᴴ T Q_k` (`hessenberg`).

* `span_arnoldiVec_Iic`: `span {q_0, …, q_j} = span {r, …, T^j r}`, the Krylov space
  `𝒦_{j+1}` (Trefethen–Bau, Lecture 33).
* `hessenberg_eq_zero`, `isUpperHessenberg_hessenberg`: `H_k` is **upper Hessenberg**
  (`h_ij = 0` for `i > j + 1`, Mathlib's `Matrix.IsUpperHessenberg`).
* `arnoldi_relation`: `T q_j = ∑_{i ≤ j + 1} h_ij q_i` whenever `j + 1 < k`, the columnwise form
  of `T Q_n = Q_{n+1} H̃_n` (Trefethen–Bau, Lecture 33).
* `hessenberg_eq_zero_of_isSymmetric`: for a symmetric (self-adjoint) `T`, `H_k` is also lower
  Hessenberg, hence **tridiagonal**: the Arnoldi iteration becomes the three-term Lanczos
  iteration (Trefethen–Bau, Lecture 36).

GMRES (`Cslib.Algorithms.NumericalLinearAlgebra.GMRES`, in CSLibExt) minimizes the residual
over `𝒦_k`; in practice it does so through the Arnoldi relation and a small Hessenberg
least-squares problem. The conjugate gradient method
(`MathlibExt.LinearAlgebra.Matrix.ConjugateGradient`) is the
corresponding method for symmetric positive definite matrices, built on Lanczos.

## References

* W. E. Arnoldi, *The principle of minimized iterations in the solution of the matrix
  eigenvalue problem*, Quart. Appl. Math. 9 (1951), 17–29.
* C. Lanczos, *An iteration method for the solution of the eigenvalue problem of linear
  differential and integral operators*, J. Res. Nat. Bur. Standards 45 (1950), 255–282.
* L. N. Trefethen, D. Bau III, *Numerical Linear Algebra*, SIAM, 1997, Lectures 33 and 36.
-/

@[expose] public section

open Submodule InnerProductSpace Set

namespace MathlibExt.Analysis.InnerProductSpace.Arnoldi

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- The Krylov vectors `r, T r, …, T^{k-1} r`. -/
def krylovVec (T : E →ₗ[𝕜] E) (r : E) (k : ℕ) (j : Fin k) : E :=
  (T ^ (j : ℕ)) r

/-- The Arnoldi vectors: the normalized Gram–Schmidt vectors of the Krylov vectors. -/
noncomputable def arnoldiVec (T : E →ₗ[𝕜] E) (r : E) (k : ℕ) : Fin k → E :=
  gramSchmidtNormed 𝕜 (krylovVec T r k)

/-- The Arnoldi matrix `H_k = Q_kᴴ T Q_k`, `h_ij = ⟪q_i, T q_j⟫`. -/
noncomputable def hessenberg (T : E →ₗ[𝕜] E) (r : E) (k : ℕ) : Matrix (Fin k) (Fin k) 𝕜 :=
  Matrix.of fun i j => ⟪arnoldiVec T r k i, T (arnoldiVec T r k j)⟫

variable {T : E →ₗ[𝕜] E} {r : E} {k : ℕ}

/-- Without breakdown, the Arnoldi vectors are orthonormal. -/
theorem orthonormal_arnoldiVec (h : LinearIndependent 𝕜 (krylovVec T r k)) :
    Orthonormal 𝕜 (arnoldiVec T r k) :=
  gramSchmidtNormed_orthonormal h

/-- `span {q_0, …, q_j} = span {r, T r, …, T^j r}`. -/
theorem span_arnoldiVec_Iic (T : E →ₗ[𝕜] E) (r : E) (j : Fin k) :
    span 𝕜 (arnoldiVec T r k '' Iic j) = span 𝕜 (krylovVec T r k '' Iic j) := by
  rw [arnoldiVec, span_gramSchmidtNormed, span_gramSchmidt_Iic]

/-- An element of the span of an orthonormal family is the sum of its components. -/
lemma eq_sum_inner_smul_of_mem_span {ι : Type*} [Fintype ι] {q : ι → E}
    (hq : Orthonormal 𝕜 q) {x : E} (hx : x ∈ span 𝕜 (range q)) :
    x = ∑ i, ⟪q i, x⟫ • q i := by
  classical
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, rfl⟩ := hy
    simp [orthonormal_iff_ite.1 hq, ite_smul]
  | zero => simp
  | add x y _ _ hx hy =>
    conv_lhs => rw [hx, hy]
    simp only [inner_add_right, add_smul, Finset.sum_add_distrib]
  | smul a x _ hx =>
    conv_lhs => rw [hx]
    simp only [inner_smul_right, Finset.smul_sum, smul_smul]

/-- `q_i` is orthogonal to the span of the `q_l` with `l ≠ i`. -/
lemma inner_eq_zero_of_mem_span {q : Fin k → E} (hq : Orthonormal 𝕜 q) {s : Set (Fin k)}
    {i : Fin k} (hi : i ∉ s) {x : E} (hx : x ∈ span 𝕜 (q '' s)) : ⟪q i, x⟫ = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    exact hq.2 (fun h => hi (h ▸ hl))
  | zero => simp
  | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
  | smul a x _ hx => rw [inner_smul_right, hx, mul_zero]

/-- `T q_j ∈ span {q_0, …, q_{j+1}}` when `j + 1 < k`. -/
theorem map_arnoldiVec_mem_span (T : E →ₗ[𝕜] E) (r : E) {j : Fin k} (hj : j.val + 1 < k) :
    T (arnoldiVec T r k j) ∈ span 𝕜 (arnoldiVec T r k '' Iic ⟨j.val + 1, hj⟩) := by
  rw [span_arnoldiVec_Iic]
  have hq : arnoldiVec T r k j ∈ span 𝕜 (krylovVec T r k '' Iic j) := by
    rw [← span_arnoldiVec_Iic]
    exact subset_span ⟨j, Set.mem_Iic.2 le_rfl, rfl⟩
  have hmap : T (arnoldiVec T r k j) ∈ (span 𝕜 (krylovVec T r k '' Iic j)).map T :=
    Submodule.mem_map_of_mem hq
  rw [Submodule.map_span] at hmap
  refine span_mono ?_ hmap
  rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
  refine ⟨⟨l.val + 1, by have := Set.mem_Iic.1 hl; omega⟩, ?_, ?_⟩
  · have := Set.mem_Iic.1 hl
    simp only [Set.mem_Iic, Fin.mk_le_mk]
    exact Nat.succ_le_succ (Fin.le_iff_val_le_val.1 this)
  · simp [krylovVec, pow_succ', Module.End.mul_apply]

/-- **The Arnoldi matrix is upper Hessenberg**: `h_ij = 0` for `i > j + 1`. -/
theorem hessenberg_eq_zero (h : LinearIndependent 𝕜 (krylovVec T r k)) {i j : Fin k}
    (hij : j.val + 1 < i.val) : hessenberg T r k i j = 0 := by
  have hj : j.val + 1 < k := hij.trans i.isLt
  refine inner_eq_zero_of_mem_span (orthonormal_arnoldiVec h) ?_
    (map_arnoldiVec_mem_span T r hj)
  simp only [Set.mem_Iic, Fin.le_iff_val_le_val, not_le]
  exact hij

/-- The Arnoldi matrix is upper Hessenberg in the sense of Mathlib's `Matrix.IsUpperHessenberg`. -/
theorem isUpperHessenberg_hessenberg (h : LinearIndependent 𝕜 (krylovVec T r k)) :
    (hessenberg T r k).IsUpperHessenberg :=
  Matrix.isUpperHessenberg_fin_iff.2 fun _ _ hij => hessenberg_eq_zero h hij

/-- **The Arnoldi relation** (Trefethen–Bau, Lecture 33): if `j + 1 < k` then
`T q_j = ∑_i h_ij q_i`, where only the terms `i ≤ j + 1` are nonzero (`hessenberg_eq_zero`). -/
theorem arnoldi_relation (h : LinearIndependent 𝕜 (krylovVec T r k)) {j : Fin k}
    (hj : j.val + 1 < k) :
    T (arnoldiVec T r k j) = ∑ i, hessenberg T r k i j • arnoldiVec T r k i := by
  have hmem : T (arnoldiVec T r k j) ∈ span 𝕜 (range (arnoldiVec T r k)) :=
    span_mono (Set.image_subset_range _ _) (map_arnoldiVec_mem_span T r hj)
  exact eq_sum_inner_smul_of_mem_span (orthonormal_arnoldiVec h) hmem

/-- **Lanczos: for symmetric `T` the Arnoldi matrix is tridiagonal**; together with
`hessenberg_eq_zero`, `h_ij = 0` whenever `|i - j| > 1`. Here: `h_ij = 0` for `j > i + 1`. -/
theorem hessenberg_eq_zero_of_isSymmetric (hT : T.IsSymmetric)
    (h : LinearIndependent 𝕜 (krylovVec T r k)) {i j : Fin k} (hij : i.val + 1 < j.val) :
    hessenberg T r k i j = 0 := by
  have h0 := hessenberg_eq_zero h hij
  simp only [hessenberg, Matrix.of_apply] at h0 ⊢
  rw [← hT, ← inner_conj_symm, h0, map_zero]

end MathlibExt.Analysis.InnerProductSpace.Arnoldi
