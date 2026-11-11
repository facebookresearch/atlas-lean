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

section EckartYoung

open scoped Matrix.Norms.Frobenius

variable {m n : ℕ}

/-- Right singular vectors of `A`: an orthonormal eigenbasis of `Aᵀ A`, ordered so that the
`i`-th vector has eigenvalue `σᵢ²` with `σ₀ ≥ σ₁ ≥ ⋯` the singular values. -/
noncomputable def rightSingularBasis (A : Matrix (Fin m) (Fin n) ℝ) :
    OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
  (Matrix.toEuclideanLin A).isSymmetric_adjoint_comp_self.eigenvectorBasis
    finrank_euclideanSpace_fin

/-- The rank-`k` truncated singular value decomposition `A Vₖ Vₖᵀ = ∑_{i<k} σᵢ uᵢ vᵢᵀ`,
where `Vₖ` collects the first `k` right singular vectors. -/
noncomputable def truncSVD (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) : Matrix (Fin m) (Fin n) ℝ :=
  A * ∑ i : Fin n with i.val < k,
    vecMulVec ⇑(rightSingularBasis A i) ⇑(rightSingularBasis A i)

/-- Subadditivity of matrix rank. -/
private theorem rank_add_bound {a b : ℕ} (M N : Matrix (Fin a) (Fin b) ℝ) :
    (M + N).rank ≤ M.rank + N.rank := by
  rw [Matrix.rank, Matrix.rank, Matrix.rank, Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

/-- A sum of matrices of rank at most one has rank at most the number of summands. -/
private theorem rank_sum_bound {a b : ℕ} {ι : Type*} (s : Finset ι)
    (M : ι → Matrix (Fin a) (Fin b) ℝ) (h : ∀ i ∈ s, (M i).rank ≤ 1) :
    (∑ i ∈ s, M i).rank ≤ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.card_insert_of_notMem hi]
    exact (rank_add_bound _ _).trans
      (by have := h i (Finset.mem_insert_self i s)
          have := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
          omega)

/-- The squared Frobenius norm is the sum of the squared entries. -/
private theorem frobenius_sq_entries {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ) :
    ‖M‖ ^ 2 = ∑ i, ∑ j, M i j ^ 2 := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt]
  · simp
  · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

/-- The squared Frobenius norm is `∑ⱼ ‖M uⱼ‖²` over any orthonormal basis `u`. -/
private theorem frobenius_sq_basis {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ)
    (u : OrthonormalBasis (Fin b) ℝ (EuclideanSpace ℝ (Fin b))) :
    ‖M‖ ^ 2 = ∑ j, ‖Matrix.toEuclideanLin M (u j)‖ ^ 2 := by
  classical
  let T := Matrix.toEuclideanLin M
  have ht (v : OrthonormalBasis (Fin b) ℝ (EuclideanSpace ℝ (Fin b))) :
      (T.adjoint ∘ₗ T).trace ℝ _ = ∑ j, ‖T (v j)‖ ^ 2 := by
    rw [LinearMap.trace_eq_sum_inner _ v]
    simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]
  rw [← ht u, ht (EuclideanSpace.basisFun (Fin b) ℝ), frobenius_sq_entries]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  simp [T, Matrix.toLpLin_apply, EuclideanSpace.basisFun_apply]

/-- The outer product `u vᵀ` maps `x` to `⟪v, x⟫ u`. -/
private theorem outer_action {b : ℕ} (u v x : EuclideanSpace ℝ (Fin b)) :
    Matrix.toEuclideanLin (vecMulVec ⇑u ⇑v) x = (inner ℝ v x) • u := by
  ext i
  simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Matrix.vecMulVec,
    PiLp.inner_apply, Finset.mul_sum, mul_assoc, mul_comm]

/-- The truncated SVD agrees with `A` on the first `k` right singular vectors and kills the
others. -/
private theorem trunc_action {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℝ)
    (k : ℕ) (j : Fin b) :
    Matrix.toEuclideanLin (truncSVD A k) (rightSingularBasis A j) =
      if j.val < k then Matrix.toEuclideanLin A (rightSingularBasis A j) else 0 := by
  classical
  have hp :
      Matrix.toEuclideanLin (∑ i : Fin b with i.val < k,
        vecMulVec ⇑(rightSingularBasis A i) ⇑(rightSingularBasis A i))
        (rightSingularBasis A j) =
          if j.val < k then rightSingularBasis A j else 0 := by
    simp only [map_sum, LinearMap.sum_apply, outer_action,
      OrthonormalBasis.inner_eq_ite, ite_smul, one_smul, zero_smul]
    simp
  simp only [truncSVD, Matrix.toEuclideanLin, Matrix.toLpLin_mul_same,
    LinearMap.comp_apply]
  rw [hp]
  split_ifs <;> simp

/-- `‖A vⱼ‖² = σⱼ²` for the right singular vectors. -/
private theorem singular_energy {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℝ) (j : Fin b) :
    ‖Matrix.toEuclideanLin A (rightSingularBasis A j)‖ ^ 2 =
      (Matrix.toEuclideanLin A).singularValues j ^ 2 := by
  rw [(Matrix.toEuclideanLin A).sq_singularValues_fin finrank_euclideanSpace_fin]
  rw [← real_inner_self_eq_norm_sq,
    ← LinearMap.adjoint_inner_left (Matrix.toEuclideanLin A)]
  change inner ℝ (((Matrix.toEuclideanLin A).adjoint ∘ₗ Matrix.toEuclideanLin A)
    (rightSingularBasis A j)) (rightSingularBasis A j) = _
  rw [rightSingularBasis, LinearMap.IsSymmetric.apply_eigenvectorBasis]
  simp [inner_smul_left]

/-- A tail sum over `Fin b` as a sum over `Finset.Ico k b`. -/
private theorem fin_tail_sum (b k : ℕ) (f : ℕ → ℝ) :
    (∑ i : Fin b with k ≤ i.val, f i.val) = ∑ i ∈ Finset.Ico k b, f i := by
  classical
  apply Finset.sum_bij (fun i _ => i.val)
  · intro i hi
    exact Finset.mem_Ico.mpr ⟨(Finset.mem_filter.mp hi).2, i.isLt⟩
  · intro i _ j _ h
    exact Fin.ext h
  · intro j hj
    refine ⟨⟨j, (Finset.mem_Ico.mp hj).2⟩, ?_, rfl⟩
    simp [(Finset.mem_Ico.mp hj).1]
  · intro i _
    rfl

/-- `∑ⱼ ‖T wⱼ‖²` through the adjoint and the standard basis. -/
private theorem energy_adjoint {a b r : ℕ}
    (T : EuclideanSpace ℝ (Fin b) →ₗ[ℝ] EuclideanSpace ℝ (Fin a))
    (w : Fin r → EuclideanSpace ℝ (Fin b)) :
    (∑ j, ‖T (w j)‖ ^ 2) =
      ∑ i, ∑ j, (inner ℝ (w j) (T.adjoint (EuclideanSpace.basisFun (Fin a) ℝ i))) ^ 2 := by
  calc
    _ = ∑ j, ∑ i, (inner ℝ (w j)
        (T.adjoint (EuclideanSpace.basisFun (Fin a) ℝ i))) ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← (EuclideanSpace.basisFun (Fin a) ℝ).sum_sq_inner_right]
      apply Finset.sum_congr rfl
      intro i _
      rw [← T.adjoint_inner_left, real_inner_comm]
    _ = _ := Finset.sum_comm

/-- Bessel: `∑ⱼ ‖M wⱼ‖² ≤ ‖M‖²` for an orthonormal family `w`. -/
private theorem orthonormal_energy_le {a b r : ℕ} (M : Matrix (Fin a) (Fin b) ℝ)
    (w : Fin r → EuclideanSpace ℝ (Fin b)) (hw : Orthonormal ℝ w) :
    (∑ j, ‖Matrix.toEuclideanLin M (w j)‖ ^ 2) ≤ ‖M‖ ^ 2 := by
  rw [energy_adjoint]
  calc
    _ ≤ ∑ i, ‖(Matrix.toEuclideanLin M).adjoint
        (EuclideanSpace.basisFun (Fin a) ℝ i)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      simpa using hw.sum_inner_products_le
        ((Matrix.toEuclideanLin M).adjoint (EuclideanSpace.basisFun (Fin a) ℝ i))
    _ = ∑ j, ‖Matrix.toEuclideanLin M (EuclideanSpace.basisFun (Fin b) ℝ j)‖ ^ 2 := by
      conv_rhs => rw [energy_adjoint]
      simp only [OrthonormalBasis.sum_sq_inner_right]
    _ = ‖M‖ ^ 2 := (frobenius_sq_basis M (EuclideanSpace.basisFun (Fin b) ℝ)).symm

/-- `‖A x‖² = ∑ᵢ σᵢ² ⟪vᵢ, x⟫²` in the right singular basis. -/
private theorem spectral_energy {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℝ)
    (x : EuclideanSpace ℝ (Fin b)) :
    ‖Matrix.toEuclideanLin A x‖ ^ 2 =
      ∑ i : Fin b, (Matrix.toEuclideanLin A).singularValues i ^ 2 *
        (inner ℝ (rightSingularBasis A i) x) ^ 2 := by
  let T := Matrix.toEuclideanLin A
  let v := rightSingularBasis A
  have h : (T.adjoint ∘ₗ T) x =
      ∑ i, (inner ℝ (v i) x) • (T.adjoint ∘ₗ T) (v i) := by
    simpa only [map_sum, map_smul] using
      congrArg (T.adjoint ∘ₗ T) (v.sum_repr' x).symm
  have hn : ‖T x‖ ^ 2 = inner ℝ ((T.adjoint ∘ₗ T) x) x := by
    rw [LinearMap.comp_apply, T.adjoint_inner_left, real_inner_self_eq_norm_sq]
  rw [hn, h, sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_smul_left]
  change _ * inner ℝ ((T.adjoint ∘ₗ T)
    (T.isSymmetric_adjoint_comp_self.eigenvectorBasis finrank_euclideanSpace_fin i)) x = _
  rw [LinearMap.IsSymmetric.apply_eigenvectorBasis, inner_smul_left,
    ← T.sq_singularValues_fin finrank_euclideanSpace_fin]
  simp only [RCLike.conj_to_real, RCLike.ofReal_real_eq_id, id_eq]
  change inner ℝ (v i) x * (T.singularValues i ^ 2 * inner ℝ (v i) x) =
    T.singularValues i ^ 2 * (inner ℝ (v i) x) ^ 2
  ring

/-- For decreasing nonnegative `d` and weights `cᵢ ∈ [0, 1]` of total at least `b - k`,
`∑_{i ≥ k} dᵢ ≤ ∑ dᵢ cᵢ`. -/
private theorem weighted_tail_le {b : ℕ} (k : ℕ) (hk : k < b)
    (d c : Fin b → ℝ) (hd : Antitone d) (hd0 : ∀ i, 0 ≤ d i)
    (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i ≤ 1)
    (hc : (b - k : ℕ) ≤ ∑ i, c i) :
    (∑ i : Fin b with k ≤ i.val, d i) ≤ ∑ i, d i * c i := by
  classical
  let t : ℝ := d ⟨k, hk⟩
  have hcount : (∑ i : Fin b, if k ≤ i.val then (1 : ℝ) else 0) = (b - k : ℕ) := by
    rw [← Finset.sum_filter]
    exact (fin_tail_sum b k (fun _ => 1)).trans (by simp)
  have hi (i : Fin b) :
      t * (c i - if k ≤ i.val then 1 else 0) ≤
        d i * c i - if k ≤ i.val then d i else 0 := by
    by_cases h : k ≤ i.val
    · have horder : d i ≤ t := hd h
      have := mul_le_mul_of_nonpos_right horder (sub_nonpos.mpr (hc1 i))
      simp only [ite_eq_left h]
      nlinarith
    · have horder : t ≤ d i := hd (show i ≤ ⟨k, hk⟩ from Nat.le_of_lt (Nat.lt_of_not_ge h))
      simpa [h] using mul_le_mul_of_nonneg_right horder (hc0 i)
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
  rw [hcount, ← Finset.sum_filter] at hs
  have ht : 0 ≤ t := hd0 ⟨k, hk⟩
  have := mul_nonneg ht (sub_nonneg.mpr hc)
  linarith

/-- The truncated SVD has rank at most `k`. -/
theorem rank_truncSVD_le (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) : (truncSVD A k).rank ≤ k := by
  classical
  unfold truncSVD
  refine (Matrix.rank_mul_le_right _ _).trans ((rank_sum_bound _ _ ?_).trans ?_)
  · intro i _
    exact Matrix.rank_vecMulVec_le _ _
  · calc
      (Finset.univ.filter fun i : Fin n => i.val < k).card ≤ (Finset.range k).card :=
        Finset.card_le_card_of_injOn Fin.val
          (fun i hi => Finset.mem_range.mpr (Finset.mem_filter.mp hi).2)
          (fun i _ j _ hij => Fin.ext hij)
      _ = k := Finset.card_range k

/-- The squared Frobenius error of the truncated SVD is the sum of the discarded squared
singular values. -/
theorem frobenius_sub_truncSVD_sq (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    ‖A - truncSVD A k‖ ^ 2 =
      ∑ i ∈ Finset.Ico k n, (Matrix.toEuclideanLin A).singularValues i ^ 2 := by
  classical
  rw [frobenius_sq_basis _ (rightSingularBasis A)]
  have he (j : Fin n) :
      ‖Matrix.toEuclideanLin (A - truncSVD A k) (rightSingularBasis A j)‖ ^ 2 =
        if k ≤ j.val then (Matrix.toEuclideanLin A).singularValues j ^ 2 else 0 := by
    simp only [map_sub, LinearMap.sub_apply, trunc_action]
    by_cases h : j.val < k
    · simp [h, not_le.mpr h]
    · simp [h, Nat.le_of_not_gt h, singular_energy]
  simp_rw [he]
  rw [← Finset.sum_filter]
  exact fin_tail_sum n k (fun i => (Matrix.toEuclideanLin A).singularValues i ^ 2)

/-- **Eckart–Young (Frobenius norm).** Every matrix of rank at most `k` has squared Frobenius
distance from `A` at least the sum of the discarded squared singular values. -/
theorem sum_sq_singularValues_le_frobenius_sub_sq (A : Matrix (Fin m) (Fin n) ℝ) {k : ℕ}
    (B : Matrix (Fin m) (Fin n) ℝ) (hB : B.rank ≤ k) :
    ∑ i ∈ Finset.Ico k n, (Matrix.toEuclideanLin A).singularValues i ^ 2 ≤ ‖A - B‖ ^ 2 := by
  classical
  by_cases hk : n ≤ k
  · rw [Finset.Ico_eq_empty_of_le hk, Finset.sum_empty]
    positivity
  have hkn : k < n := Nat.lt_of_not_ge hk
  let W := (Matrix.toEuclideanLin B).ker
  let w := stdOrthonormalBasis ℝ W
  let z : Fin (Module.finrank ℝ W) → EuclideanSpace ℝ (Fin n) := fun j => w j
  have hz : Orthonormal ℝ z := w.orthonormal.comp_linearIsometry W.subtypeₗᵢ
  have hBz (j : Fin (Module.finrank ℝ W)) : Matrix.toEuclideanLin B (z j) = 0 :=
    (w j).property
  have hbound : (∑ j, ‖Matrix.toEuclideanLin A (z j)‖ ^ 2) ≤ ‖A - B‖ ^ 2 := by
    convert orthonormal_energy_le (A - B) z hz using 1
    apply Finset.sum_congr rfl
    intro j _
    simp [map_sub, LinearMap.sub_apply, hBz]
  let c : Fin n → ℝ := fun i => ∑ j, (inner ℝ (rightSingularBasis A i) (z j)) ^ 2
  have hc0 (i : Fin n) : 0 ≤ c i :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hc1 (i : Fin n) : c i ≤ 1 := by
    simpa [c, real_inner_comm] using hz.sum_inner_products_le (rightSingularBasis A i)
  have hcsum : (∑ i, c i) = (Module.finrank ℝ W : ℝ) := by
    dsimp [c]
    rw [Finset.sum_comm]
    simp only [OrthonormalBasis.sum_sq_inner_right]
    have hn (j : Fin (Module.finrank ℝ W)) : ‖z j‖ = 1 := w.norm_eq_one j
    simp [hn]
  have hrank : Module.finrank ℝ (Matrix.toEuclideanLin B).range = B.rank := by
    exact (B.rank_eq_finrank_range_toLin (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis).symm
  have hdim : n - k ≤ Module.finrank ℝ W := by
    have hn := (Matrix.toEuclideanLin B).finrank_range_add_finrank_ker
    rw [hrank, finrank_euclideanSpace_fin] at hn
    dsimp [W]
    omega
  have hc : (n - k : ℕ) ≤ ∑ i, c i := by
    rw [hcsum]
    exact_mod_cast hdim
  have hs : (∑ j, ‖Matrix.toEuclideanLin A (z j)‖ ^ 2) =
      ∑ i : Fin n, (Matrix.toEuclideanLin A).singularValues i ^ 2 * c i := by
    simp_rw [spectral_energy]
    rw [Finset.sum_comm]
    simp only [c, Finset.mul_sum]
  have hord : Antitone (fun i : Fin n => (Matrix.toEuclideanLin A).singularValues i ^ 2) := by
    intro i j hij
    change (Matrix.toEuclideanLin A).singularValues j ^ 2 ≤
      (Matrix.toEuclideanLin A).singularValues i ^ 2
    rw [(Matrix.toEuclideanLin A).sq_singularValues_fin finrank_euclideanSpace_fin,
      (Matrix.toEuclideanLin A).sq_singularValues_fin finrank_euclideanSpace_fin]
    exact (Matrix.toEuclideanLin A).isSymmetric_adjoint_comp_self.eigenvalues_antitone
      finrank_euclideanSpace_fin hij
  rw [← fin_tail_sum n k (fun i => (Matrix.toEuclideanLin A).singularValues i ^ 2)]
  exact (weighted_tail_le k hkn _ c hord (fun _ => sq_nonneg _) hc0 hc1 hc).trans
    (hs ▸ hbound)

/-- **Eckart–Young, best-approximation form.** The truncated SVD is a best rank-`k` approximation
of `A` in the Frobenius norm: the least squared distance from `A` to a matrix of rank at most `k`
is `∑_{k ≤ i < n} σᵢ²`, attained by `truncSVD A k`. -/
theorem isLeast_frobenius_sub_sq (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    IsLeast {r | ∃ B : Matrix (Fin m) (Fin n) ℝ, B.rank ≤ k ∧ r = ‖A - B‖ ^ 2}
      (∑ i ∈ Finset.Ico k n, (Matrix.toEuclideanLin A).singularValues i ^ 2) := by
  refine ⟨⟨truncSVD A k, rank_truncSVD_le A k, (frobenius_sub_truncSVD_sq A k).symm⟩, ?_⟩
  rintro r ⟨B, hB, rfl⟩
  exact sum_sq_singularValues_le_frobenius_sub_sq A B hB

end EckartYoung


end MathlibExt.Probability.Statistics.PCA
