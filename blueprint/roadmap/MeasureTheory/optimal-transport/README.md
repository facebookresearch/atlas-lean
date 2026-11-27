# Optimal transport

Couplings of probability measures, transport costs, existence of optimal couplings, Kantorovich duality, Wasserstein distances and Brenier's theorem, displacement convexity and Wasserstein gradient flows (the JKO scheme).

- [Kantorovich duality](kantorovich-duality/README.md)
- [Monge–Kantorovich existence theorem](monge-kantorovich-existence-theorem/README.md)
- [Wasserstein distances](wasserstein-distances/README.md)
- [Brenier's theorem](brenier-s-theorem/README.md)
- [McCann's condition for displacement convexity](displacement-convexity/README.md)
- [Wasserstein gradient flows and the JKO scheme](wasserstein-gradient-flows-and-the-jko-scheme/README.md)

## Related topics

- [Total variation distance](../../Probability/convergence-of-measures/total-variation-distance/README.md):
  with the normalisation $\sup_A |\mu(A) - \nu(A)|$, total variation is the optimal transport cost for the cost
  $1_{x \ne y}$ (Villani's equation (6.11) carries a factor 2 for his total variation norm),
  and it bounds $W_1$ on bounded spaces.
- [Stochastic domination and Strassen's theorem](../../Probability/correlation-inequalities/stochastic-domination-and-strassen-s-theorem/README.md):
  Strassen's theorem is a coupling existence theorem, a transport problem with a cost valued in
  $\{0, 1\}$ (Villani, Chapter 1).
- [Matrix scaling to doubly stochastic form](../../LinearAlgebra/special-matrices/matrix-scaling-to-doubly-stochastic-form/README.md):
  the entropically regularised discrete transport plan has the form $\operatorname{diag}(u) K \operatorname{diag}(v)$ with
  $K = e^{-C/\varepsilon}$, a matrix scaling computed by Sinkhorn's algorithm (Peyré and Cuturi,
  *Computational Optimal Transport*, Proposition 4.3).
- [Concentration inequalities](../../Probability/concentration-inequalities/README.md): Talagrand's
  transport inequality bounds $W_2$ to the Gaussian measure by the relative entropy (Villani,
  Chapter 22).
- [Transport-cost inequalities](../../Probability/concentration-inequalities/transport-cost-inequalities/README.md):
  the logarithmic Sobolev inequality implies the transport inequality (Otto–Villani), and the HWI
  inequality links entropy, $W_2$ and Fisher information.
- [Fokker–Planck equation](../../Probability/stochastic-calculus/fokker-planck-equation/README.md):
  the gradient flow of the free energy for $W_2$, through the JKO scheme.
- [Equal infima without a Monge optimizer for the three-marginal Coulomb cost](three-marginal-coulomb-nonattainment.md)

- [Weak Ma–Trudinger–Wang curvature](weak-ma-trudinger-wang-curvature/README.md)
