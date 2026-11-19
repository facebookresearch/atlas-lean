/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The reduced QR factorization of a real matrix

Let `A` be a real `m × k` matrix whose `k` columns are linearly independent (full column rank;
necessarily `k ≤ m`). Then `A = Q R` where `Q` is `m × k` with orthonormal columns
(`Qᵀ Q = I`) and `R` is `k × k` upper triangular with positive diagonal; this factorization is
unique (Trefethen and Bau, *Numerical Linear Algebra*, Lecture 7, reduced QR
factorization of a full-rank matrix with `r_jj > 0`).

The factors are produced by the Gram–Schmidt process (Mathlib's `gramSchmidtNormed`) applied to
the columns `a_1, …, a_k`: `q_j` is the normalized `j`-th Gram–Schmidt vector and
`r_ij = ⟪q_i, a_j⟫` (Trefethen–Bau, Lecture 7). Numerically one computes
`Q` and `R` by modified Gram–Schmidt or by Householder triangularization (Lectures 8 and 10); in
exact arithmetic these produce the same factors up to the signs of the columns of `Q` and the
rows of `R`, and normalizing to `r_jj > 0` recovers the unique factors.

The QR factorization is the standard way to solve least-squares problems (Lecture 11, and
`Cslib.Algorithms.NumericalLinearAlgebra.LeastSquaresQR`), the first step of the QR eigenvalue
algorithm, and, in its Krylov form (the Arnoldi iteration), the engine of GMRES.

## Main definitions

* `colVec A j`: the `j`-th column of `A` as a vector of `EuclideanSpace ℝ m`.
* `qrQ A`, `qrR A`: the Gram–Schmidt factors.

## Main results

* `transpose_mul_qrQ`, `isUpperTriangular_qrR`, `qrR_diag_pos`, `eq_qrQ_mul_qrR`: the
  Gram–Schmidt factors form a reduced QR factorization.
* `exists_qr`: **existence** (Trefethen–Bau, Lecture 7, full-rank case with `r_jj > 0`).
* `qr_unique`: **uniqueness** (Trefethen–Bau, Lecture 7).
* `diag_mul_of_isUpperTriangular`: the diagonal of a product of upper triangular matrices.

## References

* L. N. Trefethen, D. Bau III, *Numerical Linear Algebra*, SIAM, 1997, Lecture 7
  (the QR factorization), Lectures 8 and 10.
* G. H. Golub, C. F. Van Loan, *Matrix Computations*, 4th ed., Johns Hopkins, 2013,
  Section 5.2.
-/

@[expose] public section

open Matrix InnerProductSpace Finset

namespace MathlibExt.LinearAlgebra.Matrix.QR

variable {m : Type*} [Fintype m] {k : ℕ}

/-- The `j`-th column of `A` as a vector of the Euclidean space `ℝ^m`. -/
noncomputable def colVec (A : Matrix m (Fin k) ℝ) (j : Fin k) : EuclideanSpace ℝ m :=
  WithLp.toLp 2 (fun i => A i j)

/-- The `Q` factor: its `j`-th column is the `j`-th normalized Gram–Schmidt vector of the
columns of `A`. -/
noncomputable def qrQ (A : Matrix m (Fin k) ℝ) : Matrix m (Fin k) ℝ :=
  Matrix.of fun i j => (gramSchmidtNormed ℝ (colVec A) j).ofLp i

/-- The `R` factor: `r_ij = ⟪q_i, a_j⟫`. -/
noncomputable def qrR (A : Matrix m (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j => inner ℝ (gramSchmidtNormed ℝ (colVec A) i) (colVec A j)

private lemma real_inner_euclidean (x y : EuclideanSpace ℝ m) :
    inner ℝ x y = ∑ i, x.ofLp i * y.ofLp i := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  simp [mul_comm]

omit [Fintype m] in
lemma linearIndependent_colVec {A : Matrix m (Fin k) ℝ} (h : LinearIndependent ℝ Aᵀ) :
    LinearIndependent ℝ (colVec A) :=
  h.map' (WithLp.linearEquiv 2 ℝ (m → ℝ)).symm.toLinearMap
    (WithLp.linearEquiv 2 ℝ (m → ℝ)).symm.ker

/-- The columns of `qrQ A` are orthonormal: `Qᵀ Q = I`. -/
theorem transpose_mul_qrQ {A : Matrix m (Fin k) ℝ} (h : LinearIndependent ℝ Aᵀ) :
    (qrQ A)ᵀ * qrQ A = 1 := by
  have hli : LinearIndependent ℝ (colVec A) := linearIndependent_colVec h
  have hon : Orthonormal ℝ (gramSchmidtNormed ℝ (colVec A)) := gramSchmidtNormed_orthonormal hli
  ext l l'
  rw [mul_apply, one_apply]
  have := (orthonormal_iff_ite.1 hon) l l'
  rw [real_inner_euclidean] at this
  simpa [qrQ] using this

/-- `qrR A` is upper triangular. -/
theorem isUpperTriangular_qrR (A : Matrix m (Fin k) ℝ) : (qrR A).IsUpperTriangular := by
  intro l j hjl
  simp only [id] at hjl
  simp only [qrR, of_apply, gramSchmidtNormed, inner_smul_left]
  rw [gramSchmidt_inv_triangular ℝ (colVec A) hjl, mul_zero]

lemma inner_gramSchmidt_self_eq (A : Matrix m (Fin k) ℝ) (j : Fin k) :
    inner ℝ (gramSchmidt ℝ (colVec A) j) (colVec A j) = ‖gramSchmidt ℝ (colVec A) j‖ ^ 2 := by
  conv_lhs => rw [gramSchmidt_def'' ℝ (colVec A) j]
  rw [inner_add_right, inner_sum, real_inner_self_eq_norm_sq, add_eq_left]
  refine sum_eq_zero fun i hi => ?_
  rw [inner_smul_right, gramSchmidt_orthogonal ℝ (colVec A) (ne_of_gt (mem_Iio.1 hi)),
    mul_zero]

/-- The diagonal of `qrR A` is positive when the columns are linearly independent:
`r_jj = ‖v_j‖`, the norm of the `j`-th Gram–Schmidt vector. -/
theorem qrR_diag_pos {A : Matrix m (Fin k) ℝ} (h : LinearIndependent ℝ Aᵀ) (j : Fin k) :
    0 < qrR A j j := by
  have hli : LinearIndependent ℝ (colVec A) := linearIndependent_colVec h
  have hne : gramSchmidt ℝ (colVec A) j ≠ 0 := gramSchmidt_ne_zero j hli
  have hpos : 0 < ‖gramSchmidt ℝ (colVec A) j‖ := norm_pos_iff.2 hne
  simp only [qrR, of_apply, gramSchmidtNormed, inner_smul_left, inner_gramSchmidt_self_eq]
  simp only [conj_trivial]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  positivity

/-- Each column is the combination of the orthonormal Gram–Schmidt vectors with coefficients
given by the corresponding column of `qrR A`. -/
lemma colVec_eq_sum {A : Matrix m (Fin k) ℝ} (h : LinearIndependent ℝ Aᵀ) (j : Fin k) :
    colVec A j = ∑ l, qrR A l j • gramSchmidtNormed ℝ (colVec A) l := by
  set e := gramSchmidtNormed ℝ (colVec A)
  have hli : LinearIndependent ℝ (colVec A) := linearIndependent_colVec h
  have hon : Orthonormal ℝ e := gramSchmidtNormed_orthonormal hli
  set K : Submodule ℝ (EuclideanSpace ℝ m) := Submodule.span ℝ (Set.range e)
  set v := colVec A j - ∑ l, qrR A l j • e l
  have hcK : colVec A j ∈ K := by
    simp only [K, e, span_gramSchmidtNormed_range, span_gramSchmidt]
    exact Submodule.subset_span ⟨j, rfl⟩
  have hsK : ∑ l, qrR A l j • e l ∈ K :=
    Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
  have hvK : v ∈ K := Submodule.sub_mem _ hcK hsK
  have hperp : ∀ l, inner ℝ (e l) v = 0 := by
    intro l
    simp only [v, inner_sub_right, hon.inner_right_fintype]
    simp [qrR, e]
  have hvperp : ∀ u ∈ K, inner ℝ u v = 0 := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx => obtain ⟨l, rfl⟩ := hx; exact hperp l
    | zero => simp
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul a x _ hx => rw [inner_smul_left, hx, mul_zero]
  have hv0 : v = 0 := inner_self_eq_zero.1 (hvperp v hvK)
  exact sub_eq_zero.1 hv0

/-- The Gram–Schmidt factors reproduce `A`: `A = Q R`. -/
theorem eq_qrQ_mul_qrR {A : Matrix m (Fin k) ℝ} (h : LinearIndependent ℝ Aᵀ) :
    A = qrQ A * qrR A := by
  ext i j
  have := congrArg (fun x : EuclideanSpace ℝ m => x.ofLp i) (colVec_eq_sum h j)
  simp only [colVec, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] at this
  rw [this, mul_apply]
  simp [qrQ, mul_comm]

/-- **Existence of the reduced QR factorization** (Trefethen–Bau, Lecture 7, full-rank case):
a real matrix with linearly independent columns is `Q R` with `Qᵀ Q = I` and `R` upper
triangular with positive diagonal. -/
theorem exists_qr (A : Matrix m (Fin k) ℝ) (h : LinearIndependent ℝ Aᵀ) :
    ∃ (Q : Matrix m (Fin k) ℝ) (R : Matrix (Fin k) (Fin k) ℝ),
      Qᵀ * Q = 1 ∧ R.IsUpperTriangular ∧ (∀ j, 0 < R j j) ∧ A = Q * R :=
  ⟨qrQ A, qrR A, transpose_mul_qrQ h, isUpperTriangular_qrR A, qrR_diag_pos h,
    eq_qrQ_mul_qrR h⟩

/-- The diagonal of a product of upper triangular matrices is the product of the diagonals. -/
theorem diag_mul_of_isUpperTriangular {U V : Matrix (Fin k) (Fin k) ℝ}
    (hU : U.IsUpperTriangular) (hV : V.IsUpperTriangular) (i : Fin k) :
    (U * V) i i = U i i * V i i := by
  rw [mul_apply, sum_eq_single i]
  · intro l _ hli
    rcases lt_or_gt_of_ne hli with hl | hl
    · rw [hU hl, zero_mul]
    · rw [hV hl, mul_zero]
  · simp

private lemma isUnit_det_of_diag_pos {R : Matrix (Fin k) (Fin k) ℝ} (hR : R.IsUpperTriangular)
    (hpos : ∀ j, 0 < R j j) : IsUnit R.det := by
  rw [det_of_isUpperTriangular hR, isUnit_iff_ne_zero]
  exact prod_ne_zero_iff.2 fun j _ => (hpos j).ne'

-- An orthogonal upper triangular matrix with positive diagonal is the identity.
private lemma eq_one_of_transpose_mul_self {U : Matrix (Fin k) (Fin k) ℝ}
    (hU : U.IsUpperTriangular) (hpos : ∀ j, 0 < U j j) (hUU : Uᵀ * U = 1) : U = 1 := by
  have hinv : U⁻¹ = Uᵀ := inv_eq_left_inv hUU
  let _ : Invertible U := invertibleOfLeftInverse _ _ hUU
  have hTup : (Uᵀ).IsUpperTriangular := hinv ▸ blockTriangular_inv_of_blockTriangular hU
  have hoff : ∀ i j, i ≠ j → U i j = 0 := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · have := hTup (i := j) (j := i) h
      simpa using this
    · exact hU h
  have hdiag : ∀ j, U j j = 1 := by
    intro j
    have := congrFun (congrFun hUU j) j
    rw [mul_apply, one_apply_eq, sum_eq_single j] at this
    · simp only [transpose_apply] at this
      nlinarith [hpos j]
    · intro l _ hl; simp [transpose_apply, hoff l j hl]
    · simp
  ext i j
  by_cases hij : i = j
  · subst hij; rw [hdiag, one_apply_eq]
  · rw [hoff i j hij, one_apply_ne hij]

/-- **Uniqueness of the reduced QR factorization** (Trefethen–Bau, Lecture 7): if
`Q R = Q' R'` with `Qᵀ Q = Q'ᵀ Q' = I` and `R`, `R'` upper triangular with positive diagonals,
then `Q = Q'` and `R = R'`. -/
theorem qr_unique {Q Q' : Matrix m (Fin k) ℝ} {R R' : Matrix (Fin k) (Fin k) ℝ}
    (hQ : Qᵀ * Q = 1) (hQ' : Q'ᵀ * Q' = 1) (hR : R.IsUpperTriangular)
    (hR' : R'.IsUpperTriangular) (hRpos : ∀ j, 0 < R j j) (hR'pos : ∀ j, 0 < R' j j)
    (h : Q * R = Q' * R') : Q = Q' ∧ R = R' := by
  have hdet := isUnit_det_of_diag_pos hR hRpos
  let _ : Invertible R := invertibleOfIsUnitDet R hdet
  have hRinv_up : (R⁻¹).IsUpperTriangular := blockTriangular_inv_of_blockTriangular hR
  have hRR : Rᵀ * R = R'ᵀ * R' := by
    calc Rᵀ * R = (Q * R)ᵀ * (Q * R) := by
          rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Qᵀ, hQ, Matrix.one_mul]
      _ = (Q' * R')ᵀ * (Q' * R') := by rw [h]
      _ = R'ᵀ * R' := by
          rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Q'ᵀ, hQ', Matrix.one_mul]
  set U := R' * R⁻¹ with hU
  have hUup : U.IsUpperTriangular := hR'.mul hRinv_up
  have hRinv_diag : ∀ j, R⁻¹ j j * R j j = 1 := by
    intro j
    rw [← diag_mul_of_isUpperTriangular hRinv_up hR, nonsing_inv_mul R hdet, one_apply_eq]
  have hUpos : ∀ j, 0 < U j j := by
    intro j
    rw [hU, diag_mul_of_isUpperTriangular hR' hRinv_up]
    have h1 := hRinv_diag j
    have h2 : 0 < R⁻¹ j j := by
      by_contra hc
      push Not at hc
      nlinarith [hRpos j]
    exact mul_pos (hR'pos j) h2
  have hUU : Uᵀ * U = 1 := by
    calc Uᵀ * U = (R⁻¹)ᵀ * (R'ᵀ * R') * R⁻¹ := by
          rw [hU, transpose_mul]; simp only [Matrix.mul_assoc]
      _ = (R⁻¹)ᵀ * (Rᵀ * R) * R⁻¹ := by rw [hRR]
      _ = (R * R⁻¹)ᵀ * (R * R⁻¹) := by
          rw [transpose_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [mul_nonsing_inv R hdet, transpose_one, Matrix.one_mul]
  have hU1 : U = 1 := eq_one_of_transpose_mul_self hUup hUpos hUU
  have hRR' : R = R' := by
    have : R' * R⁻¹ * R = R := by rw [← hU, hU1, Matrix.one_mul]
    rw [Matrix.mul_assoc, nonsing_inv_mul R hdet, Matrix.mul_one] at this
    exact this.symm
  refine ⟨?_, hRR'⟩
  rw [← hRR'] at h
  calc Q = Q * R * R⁻¹ := by rw [Matrix.mul_assoc, mul_nonsing_inv R hdet, Matrix.mul_one]
    _ = Q' * R * R⁻¹ := by rw [h]
    _ = Q' := by rw [Matrix.mul_assoc, mul_nonsing_inv R hdet, Matrix.mul_one]

end MathlibExt.LinearAlgebra.Matrix.QR
