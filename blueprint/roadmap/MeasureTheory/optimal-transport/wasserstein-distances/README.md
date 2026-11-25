# Wasserstein distances

The Wasserstein distance of order $p \ge 1$ between probability measures on a metric space is the
$p$-th root of the least transport cost $\int d(x, y)^p \, d\pi$ over couplings $\pi$. Following
Chapter 6 of Villani's *Optimal Transport: Old and New*, it is symmetric, vanishes on the diagonal,
satisfies the triangle inequality (by the gluing lemma) and separates measures, so it is an extended
metric on Borel probability measures over a Polish space; $W_p$ increases with $p$, and $W_1$
controls the integrals of Lipschitz functions.

- [Wasserstein distance](wasserstein-distance/README.md)
- [Kantorovich–Rubinstein formula](kantorovich-rubinstein-formula/README.md)
- [Wasserstein distance controlled by total variation](wasserstein-distance-and-total-variation/README.md)
- [Convergence in W_p is weak convergence with convergence of p-th moments](wasserstein-convergence/README.md)

## Related topics

- [Wasserstein gradient flows and the JKO scheme](../wasserstein-gradient-flows-and-the-jko-scheme/README.md):
  gradient flows of energies for $W_2$, discretized by minimizing movements.
- [Displacement convexity](../displacement-convexity/README.md): convexity of energies along the
  geodesics of $W_2$.
- [Mean field games](../../../GameTheory/noncooperative-games/mean-field-games/README.md): the existence theory for the mean field game system measures the dependence of the costs on the distribution of players in the Kantorovich–Rubinstein distance $W_1$.
- [Bootstrap and the Mallows metric](../../../Probability/statistical-estimation/bootstrap-and-the-mallows-metric/README.md): Bickel and Freedman's Mallows metric $d_p$ is $W_p$; its behaviour under convolution and scaling gives the asymptotic validity of the bootstrap of the mean.
