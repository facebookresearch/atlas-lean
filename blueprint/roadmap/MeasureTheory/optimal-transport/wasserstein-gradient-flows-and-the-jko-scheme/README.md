# Wasserstein gradient flows and the JKO scheme

Jordan, Kinderlehrer and Otto (1998) showed that the Fokker–Planck equation
$\partial_t \rho = \operatorname{div}(\rho \nabla \Psi) + \beta^{-1} \Delta \rho$ is the gradient flow of the
free energy $F(\rho) = \int \Psi \rho \, dx + \beta^{-1} \int \rho \log \rho \, dx$ for the quadratic
Wasserstein distance $W_2$. Since $(P_2(\mathbb{R}^n), W_2)$ is not a Riemannian manifold in the
classical sense, they made "gradient flow" precise through an implicit time discretization, the
**JKO scheme**: with time step $h > 0$, the state $\rho^{(k)}$ minimizes
$\tfrac12 W_2(\rho^{(k-1)}, \rho)^2 + h F(\rho)$. Their a priori estimates use only the metric: the
minimizer beats the previous state, which gives a discrete energy inequality and, with the triangle
and Cauchy–Schwarz inequalities, a Hölder-$\tfrac12$ bound in time. These estimates hold for an
arbitrary functional on an arbitrary metric space (the *minimizing movement* scheme). In a Hilbert
space, for a $\lambda$-convex functional and $1 + \lambda h > 0$, each step multiplies the distance
between two sequences by at most $(1 + \lambda h)^{-1}$, the discrete form of the exponential stability
of $\lambda$-convex gradient flows: a strict contraction for $\lambda > 0$, a nonexpansion for
$\lambda = 0$, and possibly a growth for $\lambda < 0$. Under the hypotheses of the linked statements,
each Wasserstein step of the Fokker–Planck free energy has a unique minimizer, and the scheme converges to
the Fokker–Planck equation as $h \to 0$.

- [Minimizing-movement scheme](minimizing-movements/README.md)
- [Discrete exponential stability of minimizing movements](contraction-of-minimizing-movements/README.md)
- [Convergence of the JKO scheme to the Fokker–Planck equation](jko-scheme/README.md)

## Related topics

- [Fokker–Planck equation](../../../Probability/stochastic-calculus/fokker-planck-equation/README.md):
  the equation whose gradient-flow structure the JKO scheme expresses; that topic proves the
  free-energy dissipation identity in one dimension.
- [Displacement convexity](../displacement-convexity/README.md): convexity of the driving
  functional along Wasserstein geodesics, which makes these gradient flows contractive.
- [Wasserstein distances](../wasserstein-distances/README.md): the metric of the scheme.
- [Ekeland variational principle](../../../Analysis/convex-analysis-and-variations/ekeland-variational-principle/README.md):
  another variational principle on complete metric spaces built from a distance penalty.
- [Langevin Monte Carlo](../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/langevin-monte-carlo/README.md): the sampling algorithm obtained by discretizing the Langevin diffusion whose law is this gradient flow; its $W_2$ convergence for strongly log-concave targets.
