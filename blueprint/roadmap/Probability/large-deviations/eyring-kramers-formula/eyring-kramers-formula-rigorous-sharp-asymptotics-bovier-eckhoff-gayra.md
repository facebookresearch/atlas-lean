# Eyring–Kramers formula for reversible diffusions

Let $X$ solve $dX(t) = -\nabla F(X(t))\,dt + \sqrt{2\varepsilon}\, dW(t)$ on $\mathbb{R}^d$, where $W$ is a standard $d$-dimensional Brownian motion (identity covariance, the noise normalization of this equation) and $F$ satisfies the growth condition (1.3) and the assumptions (H1), (ND) and (IB) of Bovier, Eckhoff, Gayrard and Klein (2004): finitely many local minima, saddle points between minima that are finite sets of isolated points, and non-degenerate Hessians at minima and saddle points. We state the confining case: in addition to these regularity, growth, gate and target hypotheses, assume $F(x) \to +\infty$ as $|x| \to \infty$. The growth bound (1.3) integrates over superlevel sets of $F$ and does not imply this confinement, and the barrier on paths to the target is no substitute for it: without it the diffusion can, with positive probability, escape to infinity without ever reaching the target, and the mean hitting time is then infinite. Let $x_i$ be a local minimum such that the set $M_i$ of the other local minima $y \ne x_i$ with $F(y) \le F(x_i)$ is nonempty, and let the barrier height relative to $M_i$ be

$$F(z^*) - F(x_i), \qquad F(z^*) = \inf_{\omega:\, \omega(0) = x_i,\ \omega(1) \in M_i}\ \sup_{t \in [0, 1]} F(\omega(t)),$$

with the infimum over continuous paths, the height of the saddle between $x_i$ and $M_i$; assume that it is attained at a unique saddle point $z^*$, with non-degenerate Hessian having exactly one negative eigenvalue $\lambda_1^*(z^*)$. The admissible targets are the sets $D = \bigcup_{y \in M_i}\overline{B_\rho(y)}$, closed balls of a fixed radius $\rho > 0$ around the minima in $M_i$, with $\rho$ so small that $D$ is disjoint from the closure of the connected component of $\{F < F(z^*)\}$ that contains $x_i$ and lies at positive distance from $z^*$. Every path from $x_i$ to $D$ then reaches the level $F(z^*)$. Let $\tau_D = \inf\{t \ge 0 : X(t) \in D\}$ be the first hitting time of the closed set $D$ by the continuous process $X$, with $\inf\emptyset = \infty$; since $x_i \notin D$, $\tau_D > 0$ almost surely under $P_{x_i}$. For such $D$, Theorem 3.2 of the source gives the Eyring–Kramers formula (Eq. (3.3))

$$E_{x_i}\tau_D = \frac{2\pi}{|\lambda_1^*(z^*)|}\sqrt{\frac{|\det\nabla^2 F(z^*)|}{\det\nabla^2 F(x_i)}}\; e^{[F(z^*) - F(x_i)]/\varepsilon}\,\bigl(1 + O(\varepsilon^{1/2}|\ln\varepsilon|)\bigr).$$

The proof rests on the sharp capacity estimate of Theorem 3.1 and the representation of mean hitting times through capacities and equilibrium potentials (Section 2).

## Depends on

- [Multidimensional Brownian motion](../../../Probability/stochastic-calculus/construction-and-sample-paths-of-brownian-motion/multidimensional-brownian-motion.md)
- [Hitting times of closed sets by continuous adapted processes are stopping times](../../../Probability/markov-chains/finite-continuous-time-markov-chains/hitting-times-of-finite-continuous-time-markov-c/hitting-times-of-closed-sets-by-continuous-adapt.md): the first hitting time $\tau_D$ of the closed target $D$, with $\inf\emptyset = \infty$

## Expansion

1. The model: the reversible diffusion on $\mathbb{R}^d$ with confining potential ($F(x) \to +\infty$ as $|x| \to \infty$), its generator and invariant measure $e^{-F/\varepsilon}$, and assumptions (H1), (ND), (IB) with the definition of saddle points through gates (Definition 1.1).
2. The potential-theoretic representation of mean hitting times, Eqs. (2.22)–(2.28).
3. Theorem 3.1: sharp asymptotics of capacities by the Dirichlet principle near the saddle points.
4. Theorem 3.2 with several saddle points, a priori regularity estimates for mean times (Section 4), and the reduction to Eq. (3.3).
5. Separate target: the general closed targets $D$ of the source, characterized by its conditions relative to the saddle $z^*$ and the lower minima.

## Sources

- A. Bovier, M. Eckhoff, V. Gayrard and M. Klein, Metastability in reversible diffusion processes I: sharp asymptotics for capacities and exit times, J. Eur. Math. Soc. 6 (2004), 399–424, Theorems 3.1 and 3.2, Eq. (3.3). <https://doi.org/10.4171/jems/14>
