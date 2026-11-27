/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Rank
public import MathlibExt.Analysis.InnerProductSpace.CourantFischer
public import MathlibExt.Analysis.InnerProductSpace.EckartYoungFrobenius

import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Principal component analysis

For an `n × p` real data matrix `X` (rows are observations, columns are variables) this file
defines the column-centered matrix, the unbiased sample covariance matrix
`S = (n - 1)⁻¹ (X - x̄)ᵀ (X - x̄)`, the principal-component scores `(X - x̄) w`, the ordered
spectral decomposition of a real symmetric matrix (eigenvalues `λ₀ ≥ λ₁ ≥ ⋯` with an
orthonormal eigenbasis, from Mathlib's spectral theorem), the Rayleigh quotient, and the
proportion of variance explained by the leading components. It proves the variational
characterization of principal components and the Eckart–Young theorem in the Frobenius norm,
the optimality statement behind PCA.

## Main results

* `sampleCov_posSemidef`, `sampleVar_scores` : `S` is positive semidefinite and the sample
  variance of the scores along `w` is `wᵀ S w`.
* `rayleigh_orderedEigenbasis`, `rayleigh_le_of_orthogonal`, `le_rayleigh_of_orthogonal` :
  Hotelling's characterization: the `k`-th principal axis maximizes the Rayleigh quotient among
  directions orthogonal to the previous axes, with maximum `λₖ`.
* `exists_le_rayleigh_of_finrank`, `exists_rayleigh_le_of_finrank` : the Courant–Fischer
  min–max and max–min principles in matrix form (from the operator statements in
  `MathlibExt.Analysis.InnerProductSpace.CourantFischer`).
* `sum_orderedEigenvalues`, `varianceExplained_le_one`, `varianceExplained_mono`,
  `varianceExplained_of_le` : the eigenvalues sum to the total variance `tr S`, and the
  proportion of variance explained by the first `k` components increases from `0` to `1`.
* `rank_truncSVD_le`, `frobenius_sub_truncSVD_sq`, `sum_sq_singularValues_le_frobenius_sub_sq`,
  `isLeast_frobenius_sub_sq` : **Eckart–Young**: the rank-`k` truncated SVD has squared
  Frobenius error `∑_{i ≥ k} σᵢ²`, and no matrix of rank at most `k` does better.

## References

* H. Hotelling, "Analysis of a complex of statistical variables into principal components",
  J. Educ. Psychol. 24 (1933), 417–441.
* C. Eckart and G. Young, "The approximation of one matrix by another of lower rank",
  Psychometrika 1 (1936), 211–218.
* I. T. Jolliffe, *Principal Component Analysis*, 2nd ed., Springer, 2002, §§2.1, 3.5.
* N. Patterson, A. L. Price and D. Reich, "Population structure and eigenanalysis", PLoS Genet.
  2 (2006), e190.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.PCA

open Matrix
open scoped InnerProductSpace
open MathlibExt.Analysis.InnerProductSpace.CourantFischer
  (rayleighForm inner_self_apply_eq_expansion exists_unit_ge_of_submodule
    exists_unit_le_of_submodule)

export Matrix.EckartYoungFrobenius (rightSingularBasis truncSVD rank_truncSVD_le
  frobenius_sub_truncSVD_sq sum_sq_singularValues_le_frobenius_sub_sq
  isLeast_frobenius_sub_sq)

/-! ### Sample covariance -/

section SampleCovariance

variable {n p : ℕ}

/-- The sample mean of column `j` of an `n × p` data matrix (rows are observations). For
`n = 0` it is the junk value `0`. -/
noncomputable def colMean (X : Matrix (Fin n) (Fin p) ℝ) (j : Fin p) : ℝ :=
  (∑ i, X i j) / n

/-- The column-centered data matrix `X i j - x̄ⱼ`. -/
noncomputable def center (X : Matrix (Fin n) (Fin p) ℝ) : Matrix (Fin n) (Fin p) ℝ :=
  Matrix.of fun i j => X i j - colMean X j

/-- The unbiased sample covariance matrix `(n - 1)⁻¹ (X - x̄)ᵀ (X - x̄)` of an `n × p` data
matrix. The divisor needs `2 ≤ n`; for `n = 1` the factor is the junk value `(0 : ℝ)⁻¹ = 0`
(and for `n = 0` the product is the zero matrix). -/
noncomputable def sampleCov (X : Matrix (Fin n) (Fin p) ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  ((n : ℝ) - 1)⁻¹ • ((center X)ᵀ * center X)

/-- The principal-component scores `(X - x̄) w` of the observations along a direction `w`. -/
noncomputable def scores (X : Matrix (Fin n) (Fin p) ℝ) (w : Fin p → ℝ) : Fin n → ℝ :=
  center X *ᵥ w

/-- The centered columns sum to zero (for at least one observation). -/
theorem sum_center (X : Matrix (Fin n) (Fin p) ℝ) (hn : 0 < n) (j : Fin p) :
    ∑ i, center X i j = 0 := by
  simp only [center, Matrix.of_apply, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, colMean]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
  ring

/-- Entries of the sample covariance matrix:
`Sⱼₖ = (n - 1)⁻¹ ∑ᵢ (Xᵢⱼ - x̄ⱼ)(Xᵢₖ - x̄ₖ)`. -/
theorem sampleCov_apply (X : Matrix (Fin n) (Fin p) ℝ) (j k : Fin p) :
    sampleCov X j k =
      ((n : ℝ) - 1)⁻¹ * ∑ i, (X i j - colMean X j) * (X i k - colMean X k) := by
  simp [sampleCov, Matrix.mul_apply, center]

/-- The sample covariance matrix is symmetric. -/
theorem sampleCov_isHermitian (X : Matrix (Fin n) (Fin p) ℝ) : (sampleCov X).IsHermitian := by
  unfold sampleCov
  refine IsHermitian.smul ?_ (IsSelfAdjoint.all _)
  have h := Matrix.isHermitian_conjTranspose_mul_self (center X)
  rwa [conjTranspose_eq_transpose_of_trivial] at h

/-- The sample covariance matrix is positive semidefinite (for every `n`). -/
theorem sampleCov_posSemidef (X : Matrix (Fin n) (Fin p) ℝ) : (sampleCov X).PosSemidef := by
  unfold sampleCov
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : (center X)ᵀ * center X = 0 := by
      ext j k
      simp [Matrix.mul_apply]
    rw [this, smul_zero]
    exact PosSemidef.zero
  · have h0 : 0 ≤ ((n : ℝ) - 1)⁻¹ := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      exact inv_nonneg.mpr (by linarith)
    have h := Matrix.posSemidef_conjTranspose_mul_self (center X)
    rw [conjTranspose_eq_transpose_of_trivial] at h
    exact h.smul h0

/-- The trace of the sample covariance matrix is the total sample variance, the sum of the
column sample variances. -/
theorem trace_sampleCov (X : Matrix (Fin n) (Fin p) ℝ) :
    (sampleCov X).trace = ∑ j, ((n : ℝ) - 1)⁻¹ * ∑ i, (X i j - colMean X j) ^ 2 := by
  simp only [Matrix.trace, Matrix.diag, sampleCov_apply, sq]

/-- The scores along any direction have sample mean zero. -/
theorem sum_scores (X : Matrix (Fin n) (Fin p) ℝ) (hn : 0 < n) (w : Fin p → ℝ) :
    ∑ i, scores X w i = 0 := by
  simp only [scores, Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  simp [← Finset.sum_mul, sum_center X hn]

/-- The sample variance of the scores along `w` is the quadratic form `wᵀ S w`. -/
theorem sampleVar_scores (X : Matrix (Fin n) (Fin p) ℝ) (w : Fin p → ℝ) :
    ((n : ℝ) - 1)⁻¹ * ∑ i, scores X w i ^ 2 = w ⬝ᵥ sampleCov X *ᵥ w := by
  simp only [sampleCov, scores, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    ← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  simp [dotProduct, sq]

end SampleCovariance

/-! ### Ordered spectral decomposition and the Rayleigh quotient -/

section Ordered

variable {p : ℕ} {S : Matrix (Fin p) (Fin p) ℝ}

/-- The eigenvalues `λ₀ ≥ λ₁ ≥ ⋯ ≥ λ_{p-1}` of a real symmetric `p × p` matrix, in decreasing
order (Mathlib's `LinearMap.IsSymmetric.eigenvalues` of `Matrix.toEuclideanLin S`). -/
noncomputable def orderedEigenvalues (hS : S.IsHermitian) : Fin p → ℝ :=
  (isSymmetric_toEuclideanLin_iff.mpr hS).eigenvalues finrank_euclideanSpace_fin

/-- An orthonormal eigenbasis of a real symmetric matrix, ordered to match
`orderedEigenvalues`; for a covariance matrix these are the principal axes. -/
noncomputable def orderedEigenbasis (hS : S.IsHermitian) :
    OrthonormalBasis (Fin p) ℝ (EuclideanSpace ℝ (Fin p)) :=
  (isSymmetric_toEuclideanLin_iff.mpr hS).eigenvectorBasis finrank_euclideanSpace_fin

/-- The Rayleigh quotient `wᵀ S w / wᵀ w` of a real matrix (junk value `0` at `w = 0`). -/
noncomputable def rayleigh (S : Matrix (Fin p) (Fin p) ℝ) (w : Fin p → ℝ) : ℝ :=
  (w ⬝ᵥ S *ᵥ w) / (w ⬝ᵥ w)

/-- The ordered eigenvalues are decreasing. -/
theorem orderedEigenvalues_antitone (hS : S.IsHermitian) : Antitone (orderedEigenvalues hS) :=
  LinearMap.IsSymmetric.eigenvalues_antitone _ _

/-- The `k`-th basis vector is an eigenvector for the `k`-th eigenvalue. -/
theorem mulVec_orderedEigenbasis (hS : S.IsHermitian) (k : Fin p) :
    S *ᵥ ⇑(orderedEigenbasis hS k) = orderedEigenvalues hS k • ⇑(orderedEigenbasis hS k) := by
  have h := (isSymmetric_toEuclideanLin_iff.mpr hS).apply_eigenvectorBasis
    finrank_euclideanSpace_fin k
  simp only [toLpLin_apply] at h
  have h' := congrArg WithLp.ofLp h
  simpa [orderedEigenbasis, orderedEigenvalues] using h'

/-- The quadratic form of a matrix as an inner product in Euclidean space. -/
private theorem dotProduct_mulVec_eq_inner (S : Matrix (Fin p) (Fin p) ℝ)
    (x : EuclideanSpace ℝ (Fin p)) :
    (⇑x ⬝ᵥ S *ᵥ ⇑x) = ⟪x, Matrix.toEuclideanLin S x⟫_ℝ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [toLpLin_apply, dotProduct_comm]

/-- `xᵀ x = ‖x‖²` in Euclidean space. -/
private theorem dotProduct_self_eq_norm_sq (x : EuclideanSpace ℝ (Fin p)) :
    (⇑x ⬝ᵥ ⇑x) = ‖x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct]
  simp

/-- The quadratic form expanded in the ordered eigenbasis: `xᵀ S x = ∑ λᵢ ⟪vᵢ, x⟫²`. -/
theorem dotProduct_mulVec_eq_sum (hS : S.IsHermitian) (x : EuclideanSpace ℝ (Fin p)) :
    (⇑x ⬝ᵥ S *ᵥ ⇑x) = ∑ i, orderedEigenvalues hS i * ⟪orderedEigenbasis hS i, x⟫_ℝ ^ 2 := by
  rw [dotProduct_mulVec_eq_inner,
    inner_self_apply_eq_expansion (isSymmetric_toEuclideanLin_iff.mpr hS)
      finrank_euclideanSpace_fin x]
  simp [orderedEigenvalues, orderedEigenbasis]

/-- The ordered eigenvalues sum to the trace. -/
theorem sum_orderedEigenvalues (hS : S.IsHermitian) :
    ∑ i, orderedEigenvalues hS i = S.trace := by
  have h := (isSymmetric_toEuclideanLin_iff.mpr hS).trace_eq_sum_eigenvalues
    finrank_euclideanSpace_fin
  simp only [RCLike.ofReal_real_eq_id, id] at h
  rw [orderedEigenvalues, ← h,
    LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun _ ℝ).toBasis]
  congr 1
  ext i j
  simp [LinearMap.toMatrix_apply, toLpLin_apply]

/-- The eigenvalues of a positive semidefinite matrix are nonnegative. -/
theorem orderedEigenvalues_nonneg (hS : S.PosSemidef) (k : Fin p) :
    0 ≤ orderedEigenvalues hS.isHermitian k := by
  have h2 := hS.dotProduct_mulVec_nonneg (⇑(orderedEigenbasis hS.isHermitian k))
  rw [mulVec_orderedEigenbasis, star_trivial, dotProduct_smul, dotProduct_self_eq_norm_sq,
    (orderedEigenbasis hS.isHermitian).orthonormal.1 k, one_pow, smul_eq_mul, mul_one] at h2
  exact h2

/-- The Rayleigh quotient of the `k`-th eigenvector is the `k`-th eigenvalue. -/
theorem rayleigh_orderedEigenbasis (hS : S.IsHermitian) (k : Fin p) :
    rayleigh S ⇑(orderedEigenbasis hS k) = orderedEigenvalues hS k := by
  rw [rayleigh, dotProduct_self_eq_norm_sq, (orderedEigenbasis hS).orthonormal.1 k,
    dotProduct_mulVec_eq_sum hS, Finset.sum_eq_single k]
  · rw [real_inner_self_eq_norm_sq, (orderedEigenbasis hS).orthonormal.1 k]
    simp
  · intro i _ hik
    rw [(orderedEigenbasis hS).orthonormal.2 hik]
    simp
  · simp

/-- **Hotelling's characterization of the principal axes.** On nonzero directions orthogonal
to the first `k` eigenvectors, the Rayleigh quotient is at most the `k`-th eigenvalue; the bound
is attained at the `k`-th eigenvector (`rayleigh_orderedEigenbasis`). -/
theorem rayleigh_le_of_orthogonal (hS : S.IsHermitian) (k : Fin p) (w : EuclideanSpace ℝ (Fin p))
    (hw : w ≠ 0) (horth : ∀ i : Fin p, i < k → ⟪orderedEigenbasis hS i, w⟫_ℝ = 0) :
    rayleigh S ⇑w ≤ orderedEigenvalues hS k := by
  have hpos : 0 < ‖w‖ ^ 2 := by positivity
  rw [rayleigh, dotProduct_self_eq_norm_sq, div_le_iff₀ hpos, dotProduct_mulVec_eq_sum hS,
    ← (orderedEigenbasis hS).sum_sq_inner_right w, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rcases lt_or_ge i k with hik | hik
  · simp [horth i hik]
  · exact mul_le_mul_of_nonneg_right (orderedEigenvalues_antitone hS hik) (sq_nonneg _)

/-- Dual of `rayleigh_le_of_orthogonal`: on nonzero directions orthogonal to the eigenvectors
after index `k`, the Rayleigh quotient is at least the `k`-th eigenvalue. -/
theorem le_rayleigh_of_orthogonal (hS : S.IsHermitian) (k : Fin p) (w : EuclideanSpace ℝ (Fin p))
    (hw : w ≠ 0) (horth : ∀ i : Fin p, k < i → ⟪orderedEigenbasis hS i, w⟫_ℝ = 0) :
    orderedEigenvalues hS k ≤ rayleigh S ⇑w := by
  have hpos : 0 < ‖w‖ ^ 2 := by positivity
  rw [rayleigh, dotProduct_self_eq_norm_sq, le_div_iff₀ hpos, dotProduct_mulVec_eq_sum hS,
    ← (orderedEigenbasis hS).sum_sq_inner_right w, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rcases lt_or_ge k i with hik | hik
  · simp [horth i hik]
  · exact mul_le_mul_of_nonneg_right (orderedEigenvalues_antitone hS hik) (sq_nonneg _)

/-- On unit vectors the Rayleigh quotient is the operator Rayleigh form of `toEuclideanLin S`. -/
private theorem rayleigh_eq_rayleighForm (S : Matrix (Fin p) (Fin p) ℝ)
    {x : EuclideanSpace ℝ (Fin p)} (hx : ‖x‖ = 1) :
    rayleigh S ⇑x = rayleighForm (Matrix.toEuclideanLin S) x := by
  rw [rayleigh, dotProduct_self_eq_norm_sq, hx, one_pow, div_one, dotProduct_mulVec_eq_inner,
    rayleighForm, real_inner_comm]
  rfl

/-- **Courant–Fischer min–max, matrix form.** Every subspace of dimension `p - k` contains a
nonzero vector whose Rayleigh quotient is at least `λₖ`. -/
theorem exists_le_rayleigh_of_finrank (hS : S.IsHermitian) (k : Fin p)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin p))) (hW : Module.finrank ℝ W = p - k) :
    ∃ w ∈ W, w ≠ 0 ∧ orderedEigenvalues hS k ≤ rayleigh S ⇑w := by
  obtain ⟨x, hxW, hx1, hle⟩ := exists_unit_ge_of_submodule
    (isSymmetric_toEuclideanLin_iff.mpr hS) finrank_euclideanSpace_fin k.isLt W hW
  refine ⟨x, hxW, by rintro rfl; simp at hx1, ?_⟩
  rw [rayleigh_eq_rayleighForm S hx1]
  exact hle

/-- **Courant–Fischer max–min, matrix form.** Every subspace of dimension `k + 1` contains a
nonzero vector whose Rayleigh quotient is at most `λₖ`. -/
theorem exists_rayleigh_le_of_finrank (hS : S.IsHermitian) (k : Fin p)
    (U : Submodule ℝ (EuclideanSpace ℝ (Fin p))) (hU : Module.finrank ℝ U = k + 1) :
    ∃ w ∈ U, w ≠ 0 ∧ rayleigh S ⇑w ≤ orderedEigenvalues hS k := by
  obtain ⟨x, hxU, hx1, hle⟩ := exists_unit_le_of_submodule
    (isSymmetric_toEuclideanLin_iff.mpr hS) finrank_euclideanSpace_fin k.isLt U hU
  refine ⟨x, hxU, by rintro rfl; simp at hx1, ?_⟩
  rw [rayleigh_eq_rayleighForm S hx1]
  exact hle

end Ordered

/-! ### Proportion of variance explained -/

section Explained

variable {n p : ℕ}

/-- The proportion of total sample variance explained by the first `k` principal components:
`(λ₀ + ⋯ + λ_{k-1}) / tr S` for the sample covariance matrix `S`. The junk value `0` is
returned when the total variance `tr S` is `0` (constant data). -/
noncomputable def varianceExplained (X : Matrix (Fin n) (Fin p) ℝ) (k : ℕ) : ℝ :=
  (∑ i : Fin p with i.val < k, orderedEigenvalues (sampleCov_isHermitian X) i) /
    (sampleCov X).trace

/-- A partial sum of the component variances is between `0` and the total variance. -/
private theorem partial_le_trace (X : Matrix (Fin n) (Fin p) ℝ) (k : ℕ) :
    0 ≤ ∑ i : Fin p with i.val < k, orderedEigenvalues (sampleCov_isHermitian X) i ∧
      ∑ i : Fin p with i.val < k, orderedEigenvalues (sampleCov_isHermitian X) i ≤
        (sampleCov X).trace := by
  have hnn : ∀ i, 0 ≤ orderedEigenvalues (sampleCov_isHermitian X) i :=
    fun i => orderedEigenvalues_nonneg (sampleCov_posSemidef X) i
  refine ⟨Finset.sum_nonneg fun i _ => hnn i, ?_⟩
  rw [← sum_orderedEigenvalues (sampleCov_isHermitian X)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun i _ _ => hnn i

/-- The proportion of variance explained is nonnegative. -/
theorem varianceExplained_nonneg (X : Matrix (Fin n) (Fin p) ℝ) (k : ℕ) :
    0 ≤ varianceExplained X k :=
  div_nonneg (partial_le_trace X k).1 ((partial_le_trace X k).1.trans (partial_le_trace X k).2)

/-- The proportion of variance explained is at most one. -/
theorem varianceExplained_le_one (X : Matrix (Fin n) (Fin p) ℝ) (k : ℕ) :
    varianceExplained X k ≤ 1 :=
  div_le_one_of_le₀ (partial_le_trace X k).2
    ((partial_le_trace X k).1.trans (partial_le_trace X k).2)

/-- Keeping more components explains more variance. -/
theorem varianceExplained_mono (X : Matrix (Fin n) (Fin p) ℝ) :
    Monotone (varianceExplained X) := by
  intro k l hkl
  refine div_le_div_of_nonneg_right ?_ ((partial_le_trace X k).1.trans (partial_le_trace X k).2)
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ =>
    orderedEigenvalues_nonneg (sampleCov_posSemidef X) i
  intro i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  omega

/-- All `p` components explain all of the variance, when the total variance is positive. -/
theorem varianceExplained_of_le (X : Matrix (Fin n) (Fin p) ℝ) {k : ℕ} (hk : p ≤ k)
    (htr : 0 < (sampleCov X).trace) : varianceExplained X k = 1 := by
  unfold varianceExplained
  have hf : (Finset.univ.filter fun i : Fin p => i.val < k) = Finset.univ :=
    Finset.filter_true_of_mem fun i _ => lt_of_lt_of_le i.isLt hk
  rw [hf, sum_orderedEigenvalues, div_self htr.ne']

end Explained

/-! ### Eckart–Young in the Frobenius norm -/



end MathlibExt.Probability.Statistics.PCA
