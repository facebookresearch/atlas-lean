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
space, a $\lambda$-convex functional makes each step a $(1 + \lambda h)^{-1}$-contraction, the
discrete form of the contraction of convex gradient flows. Each Wasserstein step has a
unique minimizer, and the scheme converges to the Fokker–Planck equation as $h \to 0$.

- [Minimizing-movement (JKO) step](is-minimizing-movement-step.md)
- [Minimizing-movement (JKO) sequence](is-minimizing-movement.md)
- [One-step energy inequality of the JKO scheme](energy-le.md)
- [The JKO step decreases the functional](le.md)
- [Tails of a minimizing-movement sequence](shift.md)
- [Discrete energy inequality, multiplied form](sum-add-le.md)
- [Discrete energy inequality of the JKO scheme](energy-sum-le.md)
- [The functional decreases along the JKO scheme](antitone.md)
- [Hölder-½ estimate of the JKO scheme](dist-sq-le.md)
- [Uniform Hölder-½ bound of the JKO scheme](dist-sq-le-of-le.md)
- [Existence of a JKO step on a proper metric space](exists-is-minimizing-movement-step.md)
- [Existence of a JKO sequence on a proper metric space](exists-is-minimizing-movement.md)
- [Variational inequality of the minimizing-movement step](inner-le.md)
- [Contraction of the minimizing-movement step](contraction.md)
- [Discrete exponential contraction of minimizing movements](contraction-pow.md)
- [Admissible densities of the JKO scheme](is-admissible.md)
- [Negative Boltzmann entropy](neg-entropy.md)
- [Potential energy](potential-energy.md)
- [Free energy of the Fokker–Planck equation](free-energy.md)
- [JKO objective](jko-objective.md)
- [JKO step](is-jkostep.md)
- [JKO sequence](is-jkosequence.md)
- [The JKO objective at the previous state](jko-objective-self.md)
- [One-step comparison inequality of the JKO scheme](jko-objective-le.md)
- [Existence and uniqueness of the JKO step](exists-unique-is-jkostep.md)
- [Convergence of the JKO scheme to the Fokker–Planck equation](tendsto-jko-fokker-planck.md)

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
