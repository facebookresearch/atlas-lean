# Wasserstein distances

The Wasserstein distance of order $p \ge 1$ between probability measures on a metric space is the
$p$-th root of the least transport cost $\int d(x, y)^p \, d\pi$ over couplings $\pi$. Following
Chapter 6 of Villani's *Optimal Transport: Old and New*, it is symmetric, vanishes on the diagonal,
satisfies the triangle inequality (by the gluing lemma) and separates measures, so it is an extended
metric on Borel probability measures over a Polish space; $W_p$ increases with $p$, and $W_1$
controls the integrals of Lipschitz functions.

- [Optimal transport cost of order $p$](transport-cost.md)
- [Every coupling bounds the transport cost](transport-cost-le-of-is-coupling.md)
- [Wasserstein distance of order $p$](wasserstein.md)
- [Wasserstein distance as an infimum over couplings](wasserstein-eq-i-inf.md)
- [Every coupling bounds the Wasserstein distance](wasserstein-le-of-is-coupling.md)
- [The product coupling](is-coupling-prod.md)
- [Swapped coupling](is-coupling-swap.md)
- [Diagonal coupling](is-coupling-diag.md)
- [Gluing lemma](exists-gluing.md)
- [Symmetry of the Wasserstein distance](wasserstein-comm.md)
- [The Wasserstein distance vanishes on the diagonal](wasserstein-self.md)
- [Wasserstein distance between Dirac masses](wasserstein-dirac.md)
- [Triangle inequality for the Wasserstein distance](wasserstein-triangle.md)
- [Monotonicity of the Wasserstein distances in the exponent](wasserstein-mono.md)
- [The Wasserstein distance is finite on measures with finite $p$-th moments](wasserstein-lt-top.md)
- [Lipschitz test functions are controlled by $W_1$](lintegral-le-add-mul-wasserstein-one.md)
- [Kantorovich–Rubinstein bound for real Lipschitz functions](enorm-integral-sub-le-mul-wasserstein-on.md)
- [Kantorovich–Rubinstein formula](wasserstein-one-eq-i-sup-lipschitz.md)
- [The Wasserstein distance separates probability measures](eq-of-wasserstein-eq-zero.md)
- [Convergence in Wasserstein distance implies weak convergence](tendsto-of-tendsto-wasserstein.md)
- [The Wasserstein distance metrizes weak convergence in $P_p$](tendsto-wasserstein-iff.md)
- [Wasserstein distance controlled by total variation](wasserstein-one-le-mul-total-variation-d.md)

## Related topics

- [Wasserstein gradient flows and the JKO scheme](../wasserstein-gradient-flows-and-the-jko-scheme/README.md):
  gradient flows of energies for $W_2$, discretized by minimizing movements.
- [Displacement convexity](../displacement-convexity/README.md): convexity of energies along the
  geodesics of $W_2$.
- [Mean field games](../../../GameTheory/noncooperative-games/mean-field-games/README.md): the existence theory for the mean field game system measures the dependence of the costs on the distribution of players in the Kantorovich–Rubinstein distance $W_1$.
- [Bootstrap and the Mallows metric](../../../Probability/statistical-estimation/bootstrap-and-the-mallows-metric/README.md): Bickel and Freedman's Mallows metric $d_p$ is $W_p$; its behaviour under convolution and scaling gives the asymptotic validity of the bootstrap of the mean.
