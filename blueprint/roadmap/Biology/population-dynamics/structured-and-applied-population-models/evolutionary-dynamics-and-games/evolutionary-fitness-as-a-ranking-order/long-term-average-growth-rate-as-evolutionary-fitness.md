# Long-term average per-capita growth rate as evolutionary fitness

In the measure framework for selection (strategies in a compact metric space $V$, bounded presence measures with densities $\eta(v, t)$), define the long-term average of the generalised reproduction coefficient

$$J_1(v) = \lim_{T \to \infty} \frac{1}{T}\int_0^T \frac{\partial_t \eta(v, t)}{\eta(v, t)}\,dt = \lim_{T \to \infty} \frac{\ln \eta(v, T)}{T}.$$

**Theorem.** Assume the limit exists for every $v$ with $\eta(v, 0) > 0$, and that every point has a neighbourhood on which the convergence is uniform. Then $J_1(v) > J_1(w)$ implies $v \succ w$; that is, $J_1$ is an evolutionary fitness.

**Corollary.** If in addition $J_1$ is continuous and $v^*$ is a global maximiser, then $J_1(v^*) = 0$: the fittest strategy has zero long-run per-capita growth.

**Example (logistic selection).** For $\partial_t \rho(v,t) = k(v)\rho - r(v)\rho\int_0^1 \rho\,dv$ with $k, r > 0$, the generalised density $\eta = \rho^{1/r(v)}$ obeys $\partial_t \eta = \big(k(v)/r(v)\big)\eta - \eta\int_0^1 \rho\,dw$, so $J = k(v)/r(v)$ is an evolutionary fitness independent of initial conditions.

## Depends on

- [Evolutionary fitness as a ranking order of strategies](ranking-order-of-strategies-and-density-ratio-criterion.md)

## Expansion

If $J_1(v) > J_1(w)$, continuity of the uniform limits gives neighbourhoods with $\inf_{O(v)} J_1 > \sup_{O(w)} J_1$, so $\eta(w',T)/\eta(v',T) = \exp\big(T(J_1(w') - J_1(v')) + o(T)\big) \to 0$ uniformly, and the density criterion applies. For the corollary, $J_1(v^*) > 0$ would make the measure of a neighbourhood of $v^*$ blow up, contradicting boundedness, while $J_1(v^*) < 0$ would make every neighbourhood, hence by compactness all of $V$, lose its measure, contradicting persistence. In the logistic example the competition integral is common to all strategies, so only $k/r$ ranks them.

## Sources

- O. Kuzenkov, A. Morozov, *Towards the construction of a mathematically rigorous framework for the modelling of evolutionary fitness*, Bull. Math. Biol. 81 (2019), 4675–4700 (Eq. (7), Theorem 2, Corollary 2.1, Example 3, Appendix C). <https://doi.org/10.1007/s11538-019-00602-3> (PMCID: PMC6874698)
