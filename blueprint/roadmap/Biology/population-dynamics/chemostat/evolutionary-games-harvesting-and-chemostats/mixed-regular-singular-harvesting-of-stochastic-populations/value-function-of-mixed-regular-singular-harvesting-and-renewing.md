# Value function of mixed regular–singular harvesting and renewing of a stochastic population

Let $\Lambda(t)$ be a continuous-time Markov chain on $\mathcal{M} = \{1,\dots,m_0\}$ (environmental regimes), independent of a Brownian motion $w$. A harvested population evolves as

$$
X(t) = x + \int_0^t b(X, \Lambda)\, ds + \int_0^t \sigma(X, \Lambda)\, dw - \int_0^t f(X, C)\, ds - Y(t) + Z(t),
$$

where $C(t)$ is a regular control with values in a compact set $\mathcal{U}$ (bounded-rate harvesting if $f > 0$, renewing if $f < 0$), and $Y, Z$ are nondecreasing impulsive controls for instantaneous harvesting and renewing. Let $\lambda \ge 0$ be a state-constraint level, $\tau = \inf\{t : X(t) < \lambda\}$, and let $a_1$ be the unit price. Let $a_2, a_3$ be the unit costs of instantaneous harvesting and renewing, with $q = a_1 - a_2$ and $r = a_1 + a_3$. Let $p(x,\alpha,c) = a_1 f(x,c) - g(x,\alpha,c)$ be the running price-minus-cost and $\delta > 0$ the discount rate. The value function is

$$
V(x,\alpha) = \sup_{(C,Y,Z)} \mathbb{E}_{x,\alpha}\Big[ \int_0^\tau e^{-\delta s} p(X, \Lambda, C)\, ds + \int_0^\tau e^{-\delta s} q\, dY - \int_0^\tau e^{-\delta s} r\, dZ \Big].
$$

**Theorem.** Assume (the source's assumption (A)): (a) the coefficients are locally Lipschitz and the controlled equation has unique nonnegative solutions; (b) $\mathcal{U}$ is compact with $0 \in \mathcal{U}$, $a_1 > a_2 > 0$, $a_3 > 0$, and $f$, $g$ are continuous and bounded with $f(\cdot, 0) = 0$.

1. (Verification) A nonnegative $\Phi(\cdot,\alpha) \in C^2$ solving the coupled quasi-variational inequalities $\max\{\mathcal{G}\Phi, q - \Phi', \Phi' - r\} \le 0$, with $\mathcal{G}\Phi = (\mathcal{L} - \delta)\Phi + \max_{c}[p - \Phi' f]$ and $\mathcal{L}$ the generator of $(X,\Lambda)$, dominates $V$.
2. (Linear growth) If $b(x,\alpha) \le \delta x + K$, then $V(x,\alpha) \le q x + M$ for a constant $M$.
3. (Lipschitz bounds) $V(x,\alpha) \ge q(x-y)^+ - r(y-x)^+ + V(y,\alpha)$ for all $x, y$, and $V$ is Lipschitz.
4. (Harvest above a threshold) If for some $U > \lambda$, $q(b - \delta(x - U)) + \sup_c(a_2 f - g) < 0$ on $(U,\infty)$, then $V(x,\alpha) = V(U,\alpha) + q(x - U)$ for $x > U$: it is optimal to harvest impulsively down to $U$.
5. (Large noise) If $\lambda > 0$, $x\, b \le K(1 + x^2)$, $b q - \delta q(x - \lambda) \le K(x^{\beta} + 1)$ for some $\beta \in (0,1)$, and $|\sigma(x,\alpha)| \ge N x$, then $V(x,\alpha) \to q(x - \lambda)$ uniformly on compacts as $N \to \infty$. The same holds under $bq - \delta q(x-\lambda) \le K$ and $|\sigma| \ge N$. So under strong environmental noise it is asymptotically optimal to harvest everything above $\lambda$ at once.
6. (Numerics) Markov chain approximation value functions $V^h$ converge to $V$ as $h \to 0$.

## Expansion

Item 3 holds because from $x > y$ one can harvest $x - y$ at once (earning $q$ per unit) and then follow a strategy from $y$, while from $x < y$ one can renew at cost $r$ per unit. Item 1 is Itô–Dynkin's formula for regime-switching diffusions with jumps from $Y$ and $Z$. Item 5 uses Lyapunov-type estimates showing that, with large multiplicative noise, the uncontrolled process hits $\lambda$ quickly, so waiting has no value and $V$ collapses to its immediate-harvest lower bound.

## Sources

- Ky Q. Tran, Bich T. N. Le, George Yin, "Harvesting of a Stochastic Population Under a Mixed Regular-Singular Control Formulation", Journal of Optimization Theory and Applications 195 (2022), 1106–1132, <https://doi.org/10.1007/s10957-022-02127-7>. Published version of arXiv:2110.14418, cited next; locators there refer to the arXiv version.
- K. Q. Tran, L. T. N. Bich, George Yin, "Harvesting of a stochastic population under a mixed regular-singular control formulation", arXiv (2021). Lemma 3.1, Theorem 3.2, Theorem 3.3, Theorem 3.4, Theorem 3.6, Theorem 3.7, Theorem 4.1. <https://doi.org/10.48550/arXiv.2110.14418>
