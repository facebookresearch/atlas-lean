# Sankoff's algorithm computes the small-parsimony cost

For all observed states $\sigma$, trees $t$ with costs and states $s$,

$$\mathrm{Sk}(t, s) = \min\{C(t, s, z) : z \text{ agrees with } \sigma\},$$

the minimum of the [total cost](edge-cost.md) over the labelings with root state $s$ that [agree](agrees.md) with $\sigma$, where the minimum over the empty set is $\infty$ (for example when $t$ is a single leaf $l$ and $s \ne \sigma(l)$).

## Sources

- D. Sankoff, *Minimal mutation trees of sequences*, SIAM J. Appl. Math. 28 (1975), 35–42.
