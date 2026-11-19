# Exact recovery by basis pursuit

In noiseless sparse regression one observes $y = X\theta^*$ with $\theta^*$ supported on a set
$S$ and more unknowns than equations. Basis pursuit, the linear program
$\min\{\|\theta\|_1 : X\theta = y\}$, replaces the combinatorial search for the sparsest solution
by a convex one. It recovers every vector supported on $S$ exactly if and only if the nullspace of
$X$ meets the cone $\mathcal{C}(S; 1)$ only at $0$, the restricted nullspace property
(Wainwright, *High-Dimensional Statistics*, 2019, §7.2.2; Hastie, Tibshirani and Wainwright,
*Statistical Learning with Sparsity*, 2015, §10.4).

- [Restricted nullspace property](restricted-nullspace.md)
- [Exact recovery by basis pursuit](basis-pursuit-unique-iff-restricted-null.md)

## Related topics

- [Lasso error bounds under restricted eigenvalues](../lasso-error-bounds-under-restricted-eigenvalues/README.md)
- [Low-rank matrix recovery](../../../Analysis/approximation-theory/low-rank-matrix-recovery/README.md): the matrix analogue, nuclear norm minimization recovering low-rank matrices under a restricted isometry property.
- [Sparse recovery under the restricted isometry property](../../../Analysis/approximation-theory/sparse-recovery-under-the-restricted-isometry-pr/README.md): Candès's sufficient condition $\delta_{2s} < \sqrt2 - 1$ on the isometry constants implies the restricted nullspace property over every support of size at most $s$, and stable and noisy versions of exact recovery.
