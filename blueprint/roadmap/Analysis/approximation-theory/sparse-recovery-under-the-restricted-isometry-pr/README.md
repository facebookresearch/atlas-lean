# Sparse recovery under the restricted isometry property

Compressed sensing recovers a sparse vector $x \in \mathbb{R}^N$ from $m \ll N$ linear measurements
$y = \Phi x$ by $\ell_1$ minimization (basis pursuit), $\min \|\tilde x\|_1$ subject to
$\Phi \tilde x = y$. The restricted isometry property asks that $\Phi$ act as a near-isometry on
sparse vectors: the isometry constant $\delta_s$ is the least $\delta$ with
$(1 - \delta) \|x\|_2^2 \le \|\Phi x\|_2^2 \le (1 + \delta) \|x\|_2^2$ for every vector with at most $s$
nonzero entries. Following Candès (C. R. Acad. Sci. Paris 2008), the chain from the definition to
exact recovery runs as follows: $\delta_{2s} < 1$ makes $s$-sparse solutions unique (no sparse
vector is lost); disjointly supported sparse vectors have nearly orthogonal images (Lemma 2.1); for
$\delta_{2s} < \sqrt2 - 1$ every kernel vector satisfies the null space property
$\|h_{T_0}\|_1 \le \rho \|h_{T_0^c}\|_1$ with $\rho = \sqrt2\, \delta_{2s} / (1 - \delta_{2s}) < 1$
(Lemma 2.2), hence the restricted nullspace property and exact recovery of every $s$-sparse vector
by basis pursuit. The stable and noisy recovery bounds of Theorems 1.2 and 1.3 control the error by
the best $s$-term approximation error and the noise level.

Random matrices with $m \gtrsim s \log(N / s)$ rows satisfy the restricted isometry property with
high probability.

- [Noiseless recovery, $\ell_2$ error](sqrt-sum-sq-sub-le-of-has-rip.md)
- [Noisy recovery](sqrt-sum-sq-sub-le-of-has-rip-of-noisy.md)
- [Noiseless recovery, $\ell_1$ error](sum-abs-sub-le-of-has-rip.md)
- [The restricted isometry property of order $s$ with constant $\delta$](has-rip.md)
- [Monotonicity of the restricted isometry property](mono.md)
- [Isometry constants are nonnegative](nonneg.md)
- [Near-orthogonality of disjointly supported sparse vectors](abs-dot-product-mul-vec-le.md)
- [Uniqueness of sparse solutions under $\delta_{2s} < 1$](eq-of-mul-vec-eq.md)
- [Exact recovery of sparse vectors by $\ell_1$ minimization](eq-of-sum-abs-le-of-has-rip.md)
- [A vector supported on a set $T$ is $|T|$-sparse](hamming-norm-le-card.md)
- [Restricted isometry implies the restricted nullspace property](restricted-nullspace-of-has-rip.md)
- [The null-space property under restricted isometry](sum-abs-le-of-mul-vec-eq-zero.md)

## Related topics

- [Exact recovery by basis pursuit](../../../Probability/linear-models-multivariate/exact-recovery-by-basis-pursuit/README.md): basis pursuit recovers every vector supported on $S$ iff the restricted nullspace property holds over $S$; the restricted isometry property with $\delta_{2s} < \sqrt2 - 1$ is a sufficient condition for it, uniform over all supports of size at most $s$.
- [Low-rank matrix recovery](../low-rank-matrix-recovery/README.md): the matrix analogue, with rank for sparsity and the nuclear norm for the $\ell_1$ norm; its restricted isometry property bounds unsquared norms.
- [Sparse recovery by orthogonal matching pursuit](../sparse-recovery-by-orthogonal-matching-pursuit/README.md): sparse recovery by a greedy algorithm under a coherence condition rather than by convex minimization.
- [Lasso error bounds under restricted eigenvalues](../../../Probability/linear-models-multivariate/lasso-error-bounds-under-restricted-eigenvalues/README.md): the statistical counterpart with noise, where a restricted eigenvalue condition on the cone plays the role of the restricted isometry property.
