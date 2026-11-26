# Monotonicity and singular limit of the optimal harvesting threshold

In the setting of [threshold optimality for ergodic harvesting with biomass-dependent quotas](threshold-optimality-for-ergodic-harvesting-with-quotas.md), assume the unimodal-drift hypotheses and $\mu(0) < \overline\mu$, so an optimal threshold $b^*$ with optimal average yield $\beta^* = G(b^*) = H(b^*)$ exists. Let $x'$ be the unique point with $G(x') = \mu(x')$, where $G(x) = \int_0^x \mu\,dm \big/ \int_0^x dm$.

**Proposition (comparison of quotas).** Let $k_1 \le k_2$ be two quotas satisfying the hypotheses, let $m_i$ be the speed measure for drift $\mu - k_i$, $H_i(x) = \int_x^\infty \mu\,dm_i \big/ \int_x^\infty dm_i$, and let $b_i$ be the unique positive solution of $G(b_i) = H_i(b_i)$. Then $b_1 \le b_2$: a more permissive quota raises the optimal harvesting threshold.

**Proposition (singular limit).** Replace the quota by $k_M = M k$ for $M \ge 1$, with optimal threshold $b^*_M$ and optimal yield $\beta^*_M$. Then

$$\lim_{M\to\infty} b^*_M = x', \qquad \lim_{M\to\infty} \beta^*_M = \mu(x').$$

The limit pair is the optimal barrier and value of the unconstrained singular ergodic harvesting problem, in which the population is reflected downward at $x'$ and the long-run yield is $\mu(x')$.

## Depends on

- [Threshold optimality for ergodic harvesting with biomass-dependent quotas](threshold-optimality-for-ergodic-harvesting-with-quotas.md)

## Expansion

$G$ does not depend on the quota, while $H_i$ is an average of $\mu$ over $[x,\infty)$ under the stationary law of the fully harvested process; comparing the two stationary laws shows $H_1 \le H_2$ on the relevant range, which moves the crossing with the increasing branch of $G$ to the right. As $M \to \infty$ the measure $m_{0,M}$ restricted to $[x,\infty)$ concentrates at $x$, so $H_M(x) \to \mu(x)$, and the crossing $G(b) = H_M(b)$ converges to the crossing $G(x') = \mu(x')$.

## Sources

- Erik Ekström, Dante Mata, Harto Saarinen, "Resource Extraction from a Stochastic Population with Harvesting Quotas", arXiv (2026). Proposition 6.1, Proposition 6.2. <https://doi.org/10.48550/arXiv.2608.17778>
