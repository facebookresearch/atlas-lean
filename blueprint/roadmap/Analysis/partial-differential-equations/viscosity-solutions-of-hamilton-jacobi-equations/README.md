# Viscosity solutions of Hamilton–Jacobi equations

Crandall and Lions introduced viscosity solutions (1983) to give first-order Hamilton–Jacobi equations $F(x, u, Du) = 0$ a theory with existence, uniqueness and stability for merely continuous solutions. A function is a subsolution when every $C^1$ test function $\varphi$ touching it from above at $x$ satisfies $F(x, u(x), D\varphi(x)) \le 0$, and a supersolution when every test function touching from below satisfies $F \ge 0$. The notion is consistent with classical solutions, is not symmetric in the sign of $F$ ($-|x|$ solves $(u')^2 - 1 = 0$, $|x|$ does not), is stable under locally uniform limits, and admits a comparison principle, proved by doubling the variables, that yields uniqueness. For convex superlinear Hamiltonians the Hopf–Lax formula gives the solution of the Cauchy problem $u_t + H(Du) = 0$ explicitly.

The pages below give the definitions, consistency with classical solutions, the eikonal example of the user's guide, stability under locally uniform limits, the comparison principle (for continuous sub- and supersolutions, in the model case $\gamma u + H(Du) = f(x)$ and under the general structure conditions of the user's guide, and for semicontinuous ones) and the Hopf–Lax formula. Perron's method, second-order equations (the theorem on sums) and half-relaxed limits lie beyond this topic.

- [Viscosity subsolution of a first-order equation](is-viscosity-subsolution.md)
- [Viscosity supersolution of a first-order equation](is-viscosity-supersolution.md)
- [Viscosity solution of a first-order equation](is-viscosity-solution.md)
- [Classical subsolutions are viscosity subsolutions](is-viscosity-subsolution-of-classical.md)
- [Classical supersolutions are viscosity supersolutions](is-viscosity-supersolution-of-classical.md)
- [Classical solutions are viscosity solutions](is-viscosity-solution-of-classical.md)
- [A $C^1$ viscosity subsolution is a classical subsolution](subsolution-le-of-cont-diff.md)
- [A $C^1$ viscosity supersolution is a classical supersolution](supersolution-le-of-cont-diff.md)
- [Consistency of viscosity and classical solutions](is-viscosity-solution-iff-of-cont-diff.md)
- [The one-dimensional eikonal Hamiltonian](eikonal.md)
- [$-|x|$ is a viscosity solution of $(u')^2 - 1 = 0$ on $\mathbb{R}$](is-viscosity-solution-neg-abs.md)
- [$|x|$ is not a viscosity supersolution of $(u')^2 - 1 = 0$](not-is-viscosity-supersolution-abs.md)
- [Stability of viscosity subsolutions under locally uniform limits](subsolution-of-tendsto-locally-uniformly-on.md)
- [Stability of viscosity supersolutions under locally uniform limits](supersolution-of-tendsto-locally-uniformly-on.md)
- [Stability of viscosity solutions under locally uniform limits](solution-of-tendsto-locally-uniformly-on.md)
- [Comparison principle for $\gamma u + H(Du) = f(x)$](comparison-principle-model-case.md)
- [Uniqueness for the Dirichlet problem for $\gamma u + H(Du) = f(x)$](eq-on-of-is-viscosity-solution.md)
- [Comparison principle for first-order equations, continuous case](comparison-principle-continuous-case.md)
- [Comparison principle for first-order equations](comparison-principle-structure-conditions.md)
- [The Hopf–Lax formula](hopf-lax-is-viscosity-solution.md)

## Related topics

- [Mean field games](../../../GameTheory/noncooperative-games/mean-field-games/README.md): the mean field game system couples a Hamilton–Jacobi–Bellman equation for the players' value with a Fokker–Planck equation for their distribution.
- [Hyperbolic motions in the N-body problem](../../ordinary-differential-equations/hyperbolic-motions-in-the-n-body-problem/README.md): Maderna and Venturelli obtain these motions from viscosity solutions of the Hamilton–Jacobi equation of the N-body problem.
- [Fenchel–Moreau theorem](../../convex-analysis-and-variations/fenchel-moreau-theorem/README.md): convex conjugation, which relates the Hamiltonian and the Lagrangian in the Hopf–Lax formula.
- [Linear quadratic regulator](../../../ComputerScience/machine-learning/reinforcement-learning/linear-quadratic-regulator/README.md): discrete-time dynamic programming, whose continuous-time counterpart is the Hamilton–Jacobi–Bellman equation solved in the viscosity sense.
