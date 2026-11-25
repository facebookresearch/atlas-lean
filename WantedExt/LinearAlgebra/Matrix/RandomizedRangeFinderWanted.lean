/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.LinearAlgebra.Matrix.RandomizedRangeFinder

/-!
# The randomized range finder (wanted)

Given a real `m × n` matrix `A`, a target rank `k` and an oversampling parameter `p`, the
randomized range finder of N. Halko, P.-G. Martinsson and J. A. Tropp (*Finding structure with
randomness: probabilistic algorithms for constructing approximate matrix decompositions*, SIAM
Rev. 53 (2011), 217–288, arXiv:0909.4061, Algorithm 4.1) draws an `n × (k + p)` standard Gaussian
test matrix `Ω`, forms the sample matrix `Y = AΩ`, and approximates `A` by `P_Y A`, where `P_Y`
is the orthogonal projection onto the range of `Y`. Its error is compared with the best rank-`k`
error, which by the Eckart–Young theorem is `(∑_{j>k} σⱼ²)^{1/2}` in the Frobenius norm and
`σ_{k+1}` in the spectral norm (`σ₁ ≥ σ₂ ≥ …` the singular values of `A`).

Here the singular values are Mathlib's `LinearMap.singularValues` of the operator
`Matrix.toEuclideanLin A : ℝⁿ → ℝᵐ`, listed in decreasing order from index `0` (so Halko,
Martinsson and Tropp's `σⱼ` is `singularValues (j - 1)`), the notion used by the Eckart–Young
pages. The Gaussian test matrix is the coordinate map of the product of standard Gaussian laws on
`Fin n × Fin (k + p)`.
The Frobenius bound is proved in the imported range-finder module.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace MathlibExt.LinearAlgebra.Matrix.RandomizedRangeFinderWanted

variable {m n : ℕ}

/-- **Average spectral error of the randomized range finder** (N. Halko, P.-G. Martinsson and
J. A. Tropp, *Finding structure with randomness*, SIAM Rev. 53 (2011), arXiv:0909.4061,
Theorem 10.6). Under the hypotheses of Theorem 10.5,
`E ‖(I - P_{AΩ}) A‖ ≤ (1 + (k / (p - 1))^{1/2}) σ_{k+1} + (e √(k + p) / p) (∑_{j>k} σⱼ²)^{1/2}`,
where `‖·‖` is the spectral (operator) norm; with 0-indexed singular values, `σ_{k+1}` is
`singularValues k`. -/
theorem_wanted integral_norm_residual_le {k p : ℕ} (hk : 2 ≤ k) (hp : 2 ≤ p)
    (hkp : k + p ≤ min m n) (A : Matrix (Fin m) (Fin n) ℝ) :
    ∫ ω, ‖residual A (Matrix.of fun i j => ω (i, j))‖ ∂(gaussianMatrixLaw n (k + p)) ≤
      (1 + Real.sqrt (k / (p - 1 : ℝ))) * (Matrix.toEuclideanLin A).singularValues k +
        Real.exp 1 * Real.sqrt (k + p : ℝ) / p *
          Real.sqrt (∑ j ∈ Finset.Ico k n, (Matrix.toEuclideanLin A).singularValues j ^ 2)

end MathlibExt.LinearAlgebra.Matrix.RandomizedRangeFinderWanted
