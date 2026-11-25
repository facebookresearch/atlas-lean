/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.QR
public import CSLibExt.MachineLearning.Regression.LeastSquares

/-!
# Linear least squares via the QR factorization

For a real `m × k` design matrix `X` and responses `y`, a least-squares solution minimizes the
residual sum of squares `rss X y θ = ‖y - X θ‖²`; by
`Cslib.MachineLearning.LeastSquares.rss_le_iff_normal` the minimizers are exactly the solutions
of the normal equations `Xᵀ X θ = Xᵀ y` (Trefethen and Bau, *Numerical Linear Algebra*,
Lecture 11, the normal equations).

Numerical linear algebra does not solve the normal equations, whose matrix `Xᵀ X` has the
squared condition number of `X`. It factors `X = Q R` with `Qᵀ Q = I` and `R` upper triangular
and solves the triangular system `R θ = Qᵀ y` (Trefethen–Bau, Lecture 11, least squares via QR).

* `rss_le_iff_of_qr`: if `X = Q R` with `Qᵀ Q = I` and `R` invertible, `θ₀` is a least-squares
  solution iff `R θ₀ = Qᵀ y`.
* `existsUnique_rss_le`: if the columns of `X` are linearly independent, the least-squares
  solution exists and is unique; it is `R⁻¹ Qᵀ y` for the reduced QR factorization
  (`MathlibExt.LinearAlgebra.Matrix.QR.exists_qr`).

## References

* L. N. Trefethen, D. Bau III, *Numerical Linear Algebra*, SIAM, 1997, Lecture 11
  (the normal equations; least squares via QR).
* G. H. Golub, C. F. Van Loan, *Matrix Computations*, 4th ed., Johns Hopkins, 2013,
  Section 5.3.
-/

@[expose] public section

open Matrix Cslib.MachineLearning.LeastSquares

namespace Cslib.Algorithms.NumericalLinearAlgebra.LeastSquaresQR

variable {m k : ℕ}

/-- **Least squares via QR** (Trefethen–Bau, Lecture 11): if `X = Q R` with `Qᵀ Q = I` and
`R` invertible, then `θ₀` minimizes `‖y - X θ‖²` iff `R θ₀ = Qᵀ y`. -/
theorem rss_le_iff_of_qr {X Q : Matrix (Fin m) (Fin k) ℝ} {R : Matrix (Fin k) (Fin k) ℝ}
    {y : Fin m → ℝ} {θ₀ : Fin k → ℝ} (hQ : Qᵀ * Q = 1) (hR : IsUnit R.det) (hX : X = Q * R) :
    (∀ θ, rss X y θ₀ ≤ rss X y θ) ↔ R *ᵥ θ₀ = Qᵀ *ᵥ y := by
  rw [rss_le_iff_normal, hX]
  have e1 : (Q * R)ᵀ *ᵥ ((Q * R) *ᵥ θ₀) = Rᵀ *ᵥ (R *ᵥ θ₀) := by
    rw [transpose_mul, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc,
      ← Matrix.mul_assoc Qᵀ, hQ, Matrix.one_mul]
  have e2 : (Q * R)ᵀ *ᵥ y = Rᵀ *ᵥ (Qᵀ *ᵥ y) := by rw [transpose_mul, mulVec_mulVec]
  rw [e1, e2]
  have hinj : Function.Injective (Rᵀ).mulVec :=
    mulVec_injective_iff_isUnit.2 ((isUnit_iff_isUnit_det _).2 (by rwa [det_transpose]))
  exact hinj.eq_iff

/-- **Existence and uniqueness of the least-squares solution** for a design matrix with linearly
independent columns (Trefethen–Bau, Lecture 11, the normal equations and least squares via QR):
exactly one `θ₀` minimizes `‖y - X θ‖²`, namely `R⁻¹ Qᵀ y` for the reduced QR factorization
`X = Q R`. -/
theorem existsUnique_rss_le (X : Matrix (Fin m) (Fin k) ℝ) (h : LinearIndependent ℝ Xᵀ)
    (y : Fin m → ℝ) : ∃! θ₀ : Fin k → ℝ, ∀ θ, rss X y θ₀ ≤ rss X y θ := by
  obtain ⟨Q, R, hQ, hRu, hpos, hX⟩ := MathlibExt.LinearAlgebra.Matrix.QR.exists_qr X h
  have hdet : IsUnit R.det := by
    rw [det_of_isUpperTriangular hRu]
    exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun j _ => (hpos j).ne')
  refine ⟨R⁻¹ *ᵥ (Qᵀ *ᵥ y), ?_, ?_⟩
  · refine (rss_le_iff_of_qr hQ hdet hX).2 ?_
    rw [mulVec_mulVec, mul_nonsing_inv R hdet, one_mulVec]
  · intro θ₀ hθ₀
    rw [rss_le_iff_of_qr hQ hdet hX] at hθ₀
    rw [← hθ₀, mulVec_mulVec, nonsing_inv_mul R hdet, one_mulVec]

end Cslib.Algorithms.NumericalLinearAlgebra.LeastSquaresQR
