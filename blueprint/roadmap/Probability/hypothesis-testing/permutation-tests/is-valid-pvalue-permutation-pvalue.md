# Validity of permutation p-values

Let a finite group $G$ act measurably on a measurable space $\Omega$ (each map $\omega \mapsto g \cdot \omega$ is measurable), and let $\mu$ be a probability measure on $\Omega$ invariant under this action. Then for every measurable statistic $T : \Omega \to \mathbb{R}$ the [permutation p-value](permutation-pvalue.md) $p_T$ is a valid p-value under $\mu$:

$$\mu(p_T \le u) \le u \quad \text{for every } u \in [0, 1].$$

## Sources

- E. L. Lehmann and J. P. Romano, *Testing Statistical Hypotheses*, 3rd ed., Springer, 2005, §15.2.
- J. Hemerik and J. Goeman, *Exact testing with random permutations*, TEST 27 (2018), 811–825.
