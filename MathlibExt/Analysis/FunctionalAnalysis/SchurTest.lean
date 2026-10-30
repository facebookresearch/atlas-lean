/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Schur's test for finite matrices

Schur's test (I. Schur, 1911) is a classical criterion for boundedness of
an operator given by a matrix: if a matrix `A` has all row sums of
`|A i j|` bounded by `R` and all column sums bounded by `C`, then `A`
acts as a bounded operator on Euclidean space (i.e. on `ℓ²` over a finite
index set) with operator norm at most `√(R * C)`.

The proof is the textbook one: for each row, a weighted Cauchy–Schwarz
inequality gives `‖(A x) i‖² ≤ R * ∑ j, ‖A i j‖ * ‖x j‖²`; summing over
`i`, swapping the finite sums, and using the column bound then gives
`‖A x‖² ≤ R * C * ‖x‖²`.

This is a companion to the bounded-operator material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/BoundedOperators.lean` and
to the integral-operator compactness of batch 59 (whose `L²` kernel
estimates are the continuous analogue of the finite sums here). It is not
one of the 72 v1 targets, and it is not in the pinned Mathlib: Mathlib has
row-sum bounds for the `ℓ^∞` operator norm (`Matrix.linfty_opNorm_def`)
and column-sum bounds for the `ℓ¹` operator norm, but no `ℓ²` Schur test.

## Main declarations

* `schur_pointwise_sq_le` : the per-row estimate.
* `schur_norm_sq_le` : the squared-norm estimate `‖A x‖² ≤ R * C * ‖x‖²`.
* `schur_apply_le` : the unsquared estimate `‖A x‖ ≤ √(R * C) * ‖x‖`.
* `norm_toEuclideanLin_le` : the canonical rectangular operator bound.
* `norm_toEuclideanCLM_le` : the canonical square operator bound.
* `norm_matrix_l2_le` : the bound for the scoped matrix L2 operator norm.
-/

@[expose] public section

open Finset Matrix

namespace MathlibExt.Analysis.FunctionalAnalysis.SchurTest

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype n] [DecidableEq n]

/-- The per-row estimate in Schur's test: the `i`-th coordinate of `A x`
satisfies `‖(A x) i‖² ≤ R * ∑ j, ‖A i j‖ * ‖x j‖²` when every row sum of
`‖A i j‖` is at most `R`. -/
theorem schur_pointwise_sq_le (A : Matrix m n 𝕜) {R : ℝ}
    (hrow : ∀ i, ∑ j, ‖A i j‖ ≤ R) (x : EuclideanSpace 𝕜 n) (i : m) :
    ‖(Matrix.toLpLin 2 2 A x) i‖ ^ 2 ≤ R * ∑ j, ‖A i j‖ * ‖x j‖ ^ 2 := by
  have hy : (Matrix.toLpLin 2 2 A x) i = ∑ j, A i j * x j := by
    simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]
  have hnorm : ‖(Matrix.toLpLin 2 2 A x) i‖ ≤ ∑ j, ‖A i j‖ * ‖x j‖ := by
    rw [hy]
    calc ‖∑ j, A i j * x j‖ ≤ ∑ j, ‖A i j * x j‖ := norm_sum_le _ _
      _ = ∑ j, ‖A i j‖ * ‖x j‖ := by simp [norm_mul]
  have hCS : (∑ j, ‖A i j‖ * ‖x j‖) ^ 2 ≤
      (∑ j, ‖A i j‖) * (∑ j, ‖A i j‖ * ‖x j‖ ^ 2) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun j => Real.sqrt ‖A i j‖) (fun j => Real.sqrt ‖A i j‖ * ‖x j‖)
    have h1 : (∑ j, Real.sqrt ‖A i j‖ * (Real.sqrt ‖A i j‖ * ‖x j‖)) =
        ∑ j, ‖A i j‖ * ‖x j‖ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← mul_assoc, Real.mul_self_sqrt (norm_nonneg _)]
    have h2 : (∑ j, (Real.sqrt ‖A i j‖) ^ 2) = ∑ j, ‖A i j‖ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Real.sq_sqrt (norm_nonneg _)]
    have h3 : (∑ j, (Real.sqrt ‖A i j‖ * ‖x j‖) ^ 2) =
        ∑ j, ‖A i j‖ * ‖x j‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_pow, Real.sq_sqrt (norm_nonneg _)]
    rwa [h1, h2, h3] at h
  calc ‖(Matrix.toLpLin 2 2 A x) i‖ ^ 2 ≤ (∑ j, ‖A i j‖ * ‖x j‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ ≤ (∑ j, ‖A i j‖) * (∑ j, ‖A i j‖ * ‖x j‖ ^ 2) := hCS
    _ ≤ R * (∑ j, ‖A i j‖ * ‖x j‖ ^ 2) :=
        mul_le_mul_of_nonneg_right (hrow i)
          (Finset.sum_nonneg fun j _ => by positivity)

variable [Fintype m]

/-- The squared-norm estimate in Schur's test: `‖A x‖² ≤ R * C * ‖x‖²`
when every row sum of `‖A i j‖` is at most `R` and every column sum is at
most `C`. -/
theorem schur_norm_sq_le (A : Matrix m n 𝕜) {R C : ℝ} (hR : 0 ≤ R)
    (hrow : ∀ i, ∑ j, ‖A i j‖ ≤ R) (hcol : ∀ j, ∑ i, ‖A i j‖ ≤ C)
    (x : EuclideanSpace 𝕜 n) :
    ‖Matrix.toLpLin 2 2 A x‖ ^ 2 ≤ R * C * ‖x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  have hmid : (∑ i, R * ∑ j, ‖A i j‖ * ‖x j‖ ^ 2) =
      R * ∑ j, (∑ i, ‖A i j‖) * ‖x j‖ ^ 2 := by
    rw [← Finset.mul_sum, Finset.sum_comm]
    apply congrArg
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_mul]
  calc ∑ i, ‖(Matrix.toLpLin 2 2 A x) i‖ ^ 2
      ≤ ∑ i, R * ∑ j, ‖A i j‖ * ‖x j‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => schur_pointwise_sq_le A hrow x i
    _ = R * ∑ j, (∑ i, ‖A i j‖) * ‖x j‖ ^ 2 := hmid
    _ ≤ R * ∑ j, C * ‖x j‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hR
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_right (hcol j) (by positivity)
    _ = R * C * ∑ j, ‖x j‖ ^ 2 := by
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring

/-- The unsquared estimate in Schur's test: `‖A x‖ ≤ √(R * C) * ‖x‖`. -/
theorem schur_apply_le (A : Matrix m n 𝕜) {R C : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hrow : ∀ i, ∑ j, ‖A i j‖ ≤ R) (hcol : ∀ j, ∑ i, ‖A i j‖ ≤ C)
    (x : EuclideanSpace 𝕜 n) :
    ‖Matrix.toLpLin 2 2 A x‖ ≤ Real.sqrt (R * C) * ‖x‖ := by
  have h := schur_norm_sq_le A hR hrow hcol x
  have hnn : 0 ≤ R * C := mul_nonneg hR hC
  calc ‖Matrix.toLpLin 2 2 A x‖
      = Real.sqrt (‖Matrix.toLpLin 2 2 A x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (R * C * ‖x‖ ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt (R * C) * ‖x‖ := by
        rw [Real.sqrt_mul hnn, Real.sqrt_sq (norm_nonneg _)]

/-- Schur's test for the canonical rectangular Euclidean matrix operator. -/
theorem norm_toEuclideanLin_le (A : Matrix m n 𝕜) {R C : ℝ}
    (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hrow : ∀ i, ∑ j, ‖A i j‖ ≤ R) (hcol : ∀ j, ∑ i, ‖A i j‖ ≤ C) :
    ‖(Matrix.toEuclideanLin A).toContinuousLinearMap‖ ≤ Real.sqrt (R * C) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro x
  exact schur_apply_le A hR hC hrow hcol x

/-- Schur's test for Mathlib's square Euclidean continuous linear map. -/
theorem norm_toEuclideanCLM_le (A : Matrix n n 𝕜) {R C : ℝ}
    (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hrow : ∀ i, ∑ j, ‖A i j‖ ≤ R) (hcol : ∀ j, ∑ i, ‖A i j‖ ≤ C) :
    ‖Matrix.toEuclideanCLM (n := n) (𝕜 := 𝕜) A‖ ≤ Real.sqrt (R * C) := by
  exact norm_toEuclideanLin_le A hR hC hrow hcol

open scoped Matrix.Norms.L2Operator in
/-- Schur's test for the actual scoped L2 operator norm of a matrix. -/
theorem norm_matrix_l2_le (A : Matrix m n 𝕜) {R C : ℝ}
    (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hrow : ∀ i, ∑ j, ‖A i j‖ ≤ R) (hcol : ∀ j, ∑ i, ‖A i j‖ ≤ C) :
    ‖A‖ ≤ Real.sqrt (R * C) := by
  exact norm_toEuclideanLin_le A hR hC hrow hcol


end MathlibExt.Analysis.FunctionalAnalysis.SchurTest
