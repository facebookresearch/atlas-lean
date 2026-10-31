/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.PCA

@[expose] public section

open Matrix MathlibExt.Probability.Statistics.PCA

namespace MathlibExtTest.Probability.Statistics.PCA

/-! ### Sample covariance of a concrete data matrix -/

/-- Four observations of two variables: `(1, 0), (-1, 0), (0, 2), (0, -2)`. Both columns have
mean `0`; the sample variances are `2/3` and `8/3` and the covariance is `0`. -/
def X : Matrix (Fin 4) (Fin 2) ℝ := !![1, 0; -1, 0; 0, 2; 0, -2]

example : colMean X 0 = 0 ∧ colMean X 1 = 0 := by
  simp [colMean, X, Fin.sum_univ_four]

example : sampleCov X 0 0 = 2 / 3 ∧ sampleCov X 1 1 = 8 / 3 ∧ sampleCov X 0 1 = 0 := by
  simp only [sampleCov_apply, colMean, X, Fin.sum_univ_four]
  norm_num

/-- Total variance `2/3 + 8/3 = 10/3`. -/
example : (sampleCov X).trace = 10 / 3 := by
  simp only [trace_sampleCov, colMean, X, Fin.sum_univ_four, Fin.sum_univ_two]
  norm_num

/-- The scores along `(0, 1)` are the second column, with sample variance `8/3 = wᵀ S w`. -/
example : (sampleCov X) *ᵥ ![0, 1] ⬝ᵥ ![0, 1] = 8 / 3 := by
  rw [dotProduct_comm, ← sampleVar_scores]
  simp only [scores, center, colMean, X, Fin.sum_univ_four, mulVec, dotProduct, of_apply,
    Fin.sum_univ_two]
  norm_num

/-- All components explain all the variance (positive total variance). -/
example : varianceExplained X 2 = 1 :=
  varianceExplained_of_le X le_rfl (by
    simp only [trace_sampleCov, colMean, X, Fin.sum_univ_four, Fin.sum_univ_two]
    norm_num)

/-- No components explain no variance. -/
example : varianceExplained X 0 = 0 := by
  simp [varianceExplained]

example (k : ℕ) : 0 ≤ varianceExplained X k ∧ varianceExplained X k ≤ 1 :=
  ⟨varianceExplained_nonneg X k, varianceExplained_le_one X k⟩

/-! ### Boundary cases and junk values -/

/-- One observation: the divisor `n - 1` is `0` and the sample covariance is the junk value `0`
(the unbiased estimator needs `n ≥ 2`). -/
example (Y : Matrix (Fin 1) (Fin 3) ℝ) : sampleCov Y = 0 := by
  simp [sampleCov]

/-- Constant data has total variance `0`, and the proportion of variance explained is the junk
value `0` for every `k`, not `1`. -/
example (k : ℕ) : varianceExplained (Matrix.of fun (_ : Fin 3) (_ : Fin 2) => (5 : ℝ)) k = 0 := by
  have h : (sampleCov (Matrix.of fun (_ : Fin 3) (_ : Fin 2) => (5 : ℝ))).trace = 0 := by
    simp only [trace_sampleCov, colMean, of_apply, Fin.sum_univ_three, Fin.sum_univ_two]
    norm_num
  simp [varianceExplained, h]

/-! ### Rayleigh quotient -/

/-- For `diag(2, 1)`, the Rayleigh quotient of `e₀` is `2` and of `(1, 1)` is `3/2`. -/
example : rayleigh !![2, 0; 0, 1] ![1, 0] = 2 ∧ rayleigh !![2, 0; 0, 1] ![1, 1] = 3 / 2 := by
  simp only [rayleigh, mulVec, dotProduct, Fin.sum_univ_two]
  norm_num

/-- The Rayleigh quotient is the junk value `0` at the zero vector. -/
example (S : Matrix (Fin 2) (Fin 2) ℝ) : rayleigh S 0 = 0 := by
  simp [rayleigh]

/-- The largest eigenvalue bounds every Rayleigh quotient (`k = 0`, no orthogonality
constraint). -/
example {S : Matrix (Fin 3) (Fin 3) ℝ} (hS : S.IsHermitian) (w : EuclideanSpace ℝ (Fin 3))
    (hw : w ≠ 0) : rayleigh S ⇑w ≤ orderedEigenvalues hS 0 :=
  rayleigh_le_of_orthogonal hS 0 w hw fun i hi => absurd hi (Fin.not_lt_zero i)

/-- The eigenvalues of a sample covariance matrix are nonnegative and decreasing. -/
example (k : Fin 2) : 0 ≤ orderedEigenvalues (sampleCov_posSemidef X).isHermitian k ∧
    orderedEigenvalues (sampleCov_isHermitian X) 1 ≤
      orderedEigenvalues (sampleCov_isHermitian X) 0 :=
  ⟨orderedEigenvalues_nonneg (sampleCov_posSemidef X) k,
    orderedEigenvalues_antitone _ (Fin.zero_le _)⟩

/-- The eigenvalues of the concrete covariance sum to its total variance `10/3`. -/
example : ∑ i, orderedEigenvalues (sampleCov_isHermitian X) i = 10 / 3 := by
  rw [sum_orderedEigenvalues, trace_sampleCov]
  simp only [colMean, X, Fin.sum_univ_four, Fin.sum_univ_two]
  norm_num

/-! ### Eckart–Young -/

open scoped Matrix.Norms.Frobenius in
/-- Keeping all `n` components reproduces the matrix exactly (empty tail sum). -/
example (A : Matrix (Fin 3) (Fin 2) ℝ) : ‖A - truncSVD A 2‖ = 0 := by
  have h := frobenius_sub_truncSVD_sq A 2
  simp only [Finset.Ico_self, Finset.sum_empty] at h
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h

open scoped Matrix.Norms.Frobenius in
/-- Rank `0` (`k = 0`): the zero matrix is the only candidate, and the bound reads
`∑ᵢ σᵢ² ≤ ‖A‖²` (in fact equality, by `frobenius_sub_truncSVD_sq`). -/
example (A : Matrix (Fin 3) (Fin 2) ℝ) :
    ∑ i ∈ Finset.Ico 0 2, (Matrix.toEuclideanLin A).singularValues i ^ 2 ≤ ‖A‖ ^ 2 := by
  simpa using sum_sq_singularValues_le_frobenius_sub_sq A (k := 0) 0 (by simp)

/-- The truncated SVD of any rank is admissible. -/
example (A : Matrix (Fin 4) (Fin 3) ℝ) : (truncSVD A 1).rank ≤ 1 := rank_truncSVD_le A 1

end MathlibExtTest.Probability.Statistics.PCA
