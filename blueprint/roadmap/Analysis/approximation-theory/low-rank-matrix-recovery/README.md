# Low-rank matrix recovery

Affine rank minimization asks for the matrix of least rank satisfying linear measurements $\mathcal{A}(X) = b$; it is NP-hard in general. Recht, Fazel and Parrilo (2010) replace the rank by the nuclear norm $\lVert X\rVert_* = \sum_i \sigma_i(X)$, its convex envelope on the unit ball of the operator norm, and prove that the two problems have the same solution when $\mathcal{A}$ satisfies a restricted isometry property on low-rank matrices, the matrix analogue of compressed sensing. Under $\delta_{2r} < 1$ the low-rank solution is unique, and under $\delta_{5r} < 1/10$ nuclear norm minimization recovers it exactly. Matrix completion, where the measurements are a uniformly random set of entries, is the case where no restricted isometry property can hold (a matrix with a single nonzero entry is invisible to most samples); Candès and Recht (2009) show that incoherence of the row and column spaces replaces it, and that nuclear norm minimization recovers a rank-$r$ $n_1 \times n_2$ matrix from $m \gtrsim n^{5/4} r \log n$ random entries with high probability ($n^{6/5}$ for ranks $r \lesssim n^{1/5}$), up to factors depending on the incoherence parameters.

- [Nuclear norm](nuclear-norm.md)
- [The nuclear norm is nonnegative](nuclear-norm-nonneg.md)
- [Restricted isometry property](is-restricted-isometry.md)
- [Subadditivity of the rank](rank-sub-le.md)
- [Uniqueness of the low-rank solution under restricted isometry](eq-of-is-restricted-isometry-two-mul.md)
- [Exact recovery by nuclear norm minimization under restricted isometry](nuclear-norm-lt-of-is-restricted-isometr.md)
- [Exact matrix completion (Candès–Recht)](exists-card-filter-unique-nuclear-norm-m.md)
- [Subadditivity of matrix rank](rank-add-le.md)
- [Rank le rank add rank sub](rank-le-rank-add-rank-sub.md)
- [Rank neg](rank-neg.md)
- [Rank sum le](rank-sum-le.md)
- [Rank sum le card](rank-sum-le-card.md)

## Related topics

- [Sparse recovery by orthogonal matching pursuit](../sparse-recovery-by-orthogonal-matching-pursuit/README.md): sparse recovery of vectors by a greedy algorithm under a coherence condition.
- [Sparse recovery under the restricted isometry property](../sparse-recovery-under-the-restricted-isometry-pr/README.md): sparse vectors are the diagonal case of low-rank matrices; on diagonal matrices the restricted isometry property of this topic becomes a vector restricted isometry property with unsquared norms, whereas Candès's isometry constants bound squared norms. The two are related but not equal: for $\delta \in [0, 1]$ a squared-norm constant $\delta$ is also an unsquared one, and an unsquared constant $\delta$ gives squared-norm bounds with constant $2\delta + \delta^2$.
- [Singular value decomposition](../../../LinearAlgebra/matrix-decompositions/singular-value-decomposition/README.md): singular values, the nuclear norm and its duality with the operator norm.
- [Exact recovery by basis pursuit](../../../Probability/linear-models-multivariate/exact-recovery-by-basis-pursuit/README.md): the exact vector analogue of nuclear norm recovery, $\ell_1$ minimization recovering sparse vectors, characterized by the restricted nullspace property.
