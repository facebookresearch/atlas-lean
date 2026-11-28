# Heat equation

The heat equation $u_t - \Delta u = 0$ is the model parabolic equation. Its fundamental solution
$\Phi(t, x) = (4 \pi t)^{-n/2} e^{-|x|^2/(4t)}$ is positive, has total mass one and solves the
equation for $t > 0$; convolving it with initial data solves the Cauchy problem on $\mathbb{R}^n$.
On a bounded domain, the weak maximum principle places the maximum of a (sub)solution on the
parabolic boundary of the space-time cylinder, which gives uniqueness for the initial-boundary
value problem.

The pages below give the properties of $\Phi$ in every finite dimension, the weak maximum principle for
subsolutions, uniqueness on bounded domains, and the one-dimensional Cauchy problem.

- [Heat-kernel solution](heat-solution.md)
- [The one-dimensional heat solution as a heat-kernel convolution](heat-solution-eq-kernel.md)
- [The Gaussian heat kernel solves the heat equation](heat-kernel-solves-heat-equation.md)
- [Fundamental solution of the heat equation](heat-kernel.md)
- [The heat kernel is positive](heat-kernel-pos.md)
- [The heat kernel has total mass one](integral-heat-kernel.md)
- [The heat kernel is integrable](integrable-heat-kernel.md)
- [Time derivative of the heat kernel](has-deriv-at-heat-kernel-time.md)
- [Laplacian of the heat kernel](laplacian-heat-kernel.md)
- [The heat kernel solves the heat equation](heat-kernel-has-deriv-at-time-eq-laplaci.md)
- [Parabolic boundary of a space-time cylinder](parabolic-boundary.md)
- [Weak maximum principle for the heat equation](exists-mem-parabolic-boundary-is-max-on.md)
- [Uniqueness for the heat equation on a bounded domain](eq-on-of-heat-equation.md)
- [Single-mode solution of the Dirichlet heat equation](single-mode-solution-of-the-dirichlet-heat-equation.md)
- [Uniqueness of the Gaussian heat solution in the exponential-growth class](eq-heat-solution-of-exp-growth.md)
- [The Gaussian heat solution has exponential growth on every strip](heat-solution-has-exp-growth-on-strip.md)
- [Fick diffusion](fick-diffusion/README.md)

## Related topics

- [Wasserstein gradient flows and the JKO scheme](../../../MeasureTheory/optimal-transport/wasserstein-gradient-flows-and-the-jko-scheme/README.md):
  with zero potential the Fokker–Planck equation is the heat equation, the Wasserstein gradient flow
  of the Boltzmann entropy (Jordan, Kinderlehrer and Otto).
- [Fokker–Planck equation](../../../Probability/stochastic-calculus/fokker-planck-equation/README.md):
  the drift–diffusion equation that reduces to the heat equation without drift.

- [Heat convolution](heat-convolution.md)

- [The heat convolution preserves the constant one](heat-convolution-const-one.md)

- [The heat convolution solves the heat equation](heat-convolution-satisfies-heat-equation.md)

- [The heat convolution is smooth at positive time](heat-convolution-smooth.md)

- [The heat semigroup's generator is the Laplacian](heat-semigroup-generator-eq-laplacian.md)

- [The heat semigroup's generator is the Laplacian, in `ENNReal`](heat-semigroup-generator-eq-laplacian-en.md)
