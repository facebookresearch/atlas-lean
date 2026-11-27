# Weak well-posedness of the Wright–Fisher SPDE with irregular drift

**Equation.** For an allele frequency field $u_t(x) \in [0, 1]$, $t \ge 0$, $x \in \mathbb{R}$, consider the one-dimensional Wright–Fisher stochastic heat equation

$$\partial_t u_t = \tfrac12 \Delta u_t + b(u_t) + \sqrt{u_t(1 - u_t)}\, \dot W, \qquad u_0 = f,$$

where $\dot W$ is space-time white noise and $f \in \mathcal C(\mathbb{R}, [0, 1])$. The drift is a power series with a possible jump at $1$,

$$b(z) = \sum_{k=0}^\infty b_k z^k + b_\infty \mathbf 1_{\{1\}}(z), \qquad z \in [0, 1],$$

with real coefficients $(b_k)_{k \in \mathbb{N} \cup \{\infty\}}$ satisfying $b(0) \ge 0 \ge b(1) > -\infty$.

**Theorem.** If there is $R \ge 1$ such that

$$b_1 \le -\sum_{k \in \bar{\mathbb N} \setminus \{1\}} |b_k|\, R^{k-1},$$

then the equation is weakly well posed: a $[0, 1]$-valued continuous weak solution exists and its law is unique.

The class contains drifts that are non-Lipschitz or discontinuous exactly where the noise coefficient degenerates, for example $b(u) = u^q(1 - u)$ for every $q \in (0, 1)$ (Hölder drift near $0$) and $b(u) = \mathbf 1_{(0,1]}(u) - u$ (discontinuous at $u = 0$), where pathwise uniqueness arguments fail.

## Expansion

Uniqueness in law comes from a moment duality. For products $\prod_i u_t(x_i)$ the dual is a branching–coalescing Brownian particle system: particles move as Brownian motions, pairs coalesce at rate given by their intersection local time (the dual of the Wright–Fisher noise), and each particle branches at rate $\mu$ into a random number of offspring in $\bar{\mathbb N} = \mathbb N \cup \{\infty\}$ with an offspring law built from the coefficients $b_k$, and the remaining drift contributes an exponential weight to the duality formula. The coefficient condition with radius $R$ makes the exponential weight in the duality formula integrable, using that coalescence keeps the expected number of particles bounded on finite time intervals (a $C N_0/\sqrt{s}$ bound). Existence follows by approximation with smooth drifts and tightness.

## Sources

- Clayton Barnes, Leonid Mytnik and Zhenyao Sun, "Wright–Fisher stochastic heat equations with irregular drifts", Probab. Theory Related Fields 194 (2026), 1711–1786, <https://doi.org/10.1007/s00440-025-01398-1>. Numbering follows the arXiv version, arXiv:2402.11160 (2024): Theorem 1.1, Theorem 1.4 and Proposition 2.2, <https://doi.org/10.48550/arXiv.2402.11160>.
