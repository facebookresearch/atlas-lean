# Log-growth criteria for stochastic single-species models

**Setting.** A population density $X_t \ge 0$ evolves as

$$X_{t+1} = X_t\, f(X_t, \xi_{t+1}),$$

where $(\xi_t)$ is an i.i.d. sequence in a separable metric space $E$ and the fitness $f : [0,\infty) \times E \to (0,\infty)$ is continuous, so $(X_t)$ is a Markov chain. Write $f(\infty, \xi) = \lim_{x\to\infty} f(x, \xi)$ when $f$ is monotone in $x$, and assume the expectations $\mathbb E[\log f(0,\xi)]$, $\mathbb E[\log f(\infty,\xi)]$ are defined.

**Theorem (negative density dependence).** Suppose $f(x, \xi)$ is decreasing in $x$ for every $\xi$. Then, with probability one,

- if $\mathbb E[\log f(0,\xi)] < 0$: $X_t \to 0$ for every $X_0 \ge 0$ (extinction);
- if $\mathbb E[\log f(\infty,\xi)] > 0$: $X_t \to \infty$ for every $X_0 > 0$ (unbounded growth);
- if $\mathbb E[\log f(0,\xi)] > 0 > \mathbb E[\log f(\infty,\xi)]$: the population is stochastically persistent: for every $\varepsilon > 0$ there is $M > 0$ such that the long-run fraction of time spent in $[1/M, M]$ is at least $1 - \varepsilon$, for every $X_0 > 0$.

**Theorem (positive density dependence).** Suppose $f(x, \xi)$ is increasing in $x$ for every $\xi$ (an Allee effect). Then, with probability one,

- if $\mathbb E[\log f(\infty,\xi)] < 0$: $X_t \to 0$ for every $X_0 \ge 0$;
- if $\mathbb E[\log f(0,\xi)] > 0$: $X_t \to \infty$ for every $X_0 > 0$;
- if $\mathbb E[\log f(0,\xi)] < 0 < \mathbb E[\log f(\infty,\xi)]$: *conditional persistence*: for any $0 < \delta < 1$ there are $m, M > 0$ with $\Pr(X_t \to 0 \mid X_0 = y) \ge 1 - \delta$ for $y \in (0, m]$ and $\Pr(X_t \to \infty \mid X_0 = x) \ge 1 - \delta$ for $x \ge M$; if moreover $\{0, \infty\}$ is accessible from $(0, \infty)$, $X_t$ converges to $0$ or $\infty$ almost surely.

Examples: stochastic Ricker and Beverton–Holt models fall under the first theorem; mate limitation and predator saturation under the second.

## Proof depends on

- [Strong law of large numbers from the ergodic theorem](../../../../Dynamics/ergodic-theory/birkhoff-ergodic-theorem/tendsto-average-coordinates-ae.md)

## Expansion

The quantity $\mathbb E[\log f(x,\xi)]$ is the long-run per-capita log growth rate of a population held at density $x$. Monotonicity in $x$ sandwiches $\log X_t$ between random walks with drifts $\mathbb E\log f(0,\cdot)$ and $\mathbb E\log f(\infty,\cdot)$; the strong law of large numbers then settles the extinction and growth cases, while in the mixed cases the random walk comparison applies only near $0$ or near $\infty$, giving persistence (negative feedback pushes back) or conditional outcomes (positive feedback amplifies departures).

## Sources

- G. Roth and S. J. Schreiber, "Pushed beyond the brink: Allee effects, environmental stochasticity, and extinction", *Journal of Biological Dynamics* (2014), Section 2 (standing assumptions), Theorem 3.1 (from earlier work of Schreiber) and Theorem 3.2, with the Ricker, Beverton–Holt, mate-limitation and predator-saturation examples. <https://doi.org/10.1080/17513758.2014.962631> (PMC4241649)
