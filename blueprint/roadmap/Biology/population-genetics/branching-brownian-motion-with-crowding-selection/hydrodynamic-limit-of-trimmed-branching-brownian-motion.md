# Hydrodynamic limit of trimmed branching Brownian motion

**Particle system.** For $n \in \mathbb{N}$ and $\varepsilon > 0$, $n$ particles on $\mathbb{R}$ move as independent diffusions $dX = b(X)\,dt + dW$ with a bounded, possibly discontinuous (càdlàg) drift $b$. Each particle branches at rate $1$ into two; at every branching event one particle is removed from a most crowded cell of the partition $\{[k\varepsilon,(k+1)\varepsilon) : k \in \mathbb{Z}\}$, so the number of particles stays $n$. Let $\mu^{n,\varepsilon}_t$ be the empirical probability measure and $\beta^{n,\varepsilon}$ the normalized space–time measure of removal events (total mass $t$ on $[0,t]\times\mathbb{R}$).

**Limit problem.** A pair $(u,\beta)$, with $u(t,\cdot)$ a continuous probability density and $\beta$ a measure on $[0,\infty)\times\mathbb{R}$ with $\beta([0,t]\times\mathbb{R}) = t$, solves the free obstacle problem

$$

\partial_t u = \tfrac12\,\partial_{xx} u - \partial_x(b\,u) + u - \beta

$$

weakly, with $\beta(dt,dx) = \beta_t(dx)\,dt$ and, for almost every $t$, the probability measure $\beta_t$ supported on the set of spatial maximizers of $u(t,\cdot)$.

**Theorem.**

1. (Hydrodynamic limit.) There is a sequence $\varepsilon_n \to 0$ such that $(\mu^{n,\varepsilon_n},\beta^{n,\varepsilon_n})$ converges in probability to a deterministic limit $(\mu,\beta)$; $\mu_t$ has a density $u(t,\cdot)$, and $(u,\beta)$ is the unique solution of the free obstacle problem in the class of continuous densities considered.
2. (Inverse problem.) For every compactly supported Borel probability measure $\beta_0$ with $\beta_0([x_-,x_+]) = 1$, put $c = (\sqrt2 + x_+ - x_-)^{-1}$, $u_0(x) = c\,e^{-\sqrt2\,\mathrm{dist}(x,[x_-,x_+])}$ and

$$

b(x) = \begin{cases} \sqrt2, & x < x_-,\\ \big(x - \tfrac{x_+ + x_-}{2}\big) + \dfrac{1 - 2\beta_0((-\infty,x])}{2c}, & x_- \le x < x_+,\\ -\sqrt2, & x \ge x_+. \end{cases}

$$

Then $u(t,x) = u_0(x)$, $\beta = dt \otimes \beta_0$ is the stationary solution, and the particle system started near $u_0$ converges to it. So every compactly supported removal profile is realized by some drift.

## Expansion

Tightness of the empirical measures comes from the bounded drift and from domination by a branching system without removal, whose expected density $v$ (of mass $e^t$) bounds every subsequential limit; this gives densities. Removal from the most crowded cell means removal from near-maximal density, so as $\varepsilon_n \to 0$ slowly the removal measure concentrates on the argmax of $u(t,\cdot)$. Uniqueness for the obstacle problem with discontinuous drift identifies all limits. For the inverse problem, on $[x_-,x_+]$ the density is constant, so stationarity reduces to $\partial_x(bu) = u - \beta_0$, which is solved by the stated affine-plus-distribution-function drift; outside the interval the drift $\pm\sqrt2$ gives the exponential tails $e^{-\sqrt2\,\mathrm{dist}}$.

## Sources

- Rami Atar, Leonid Mytnik, Dominic T. Schickentanz, "Trimmed Branching Brownian Motion with Discontinuous Drift", arXiv (2026). Section 1 (Theorems 1–2), Sections 3–4 (Proposition 5). <https://doi.org/10.48550/arXiv.2611.26579>
