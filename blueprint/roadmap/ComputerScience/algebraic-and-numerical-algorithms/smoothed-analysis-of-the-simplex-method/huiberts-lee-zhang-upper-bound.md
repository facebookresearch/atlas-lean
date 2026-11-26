# Huiberts-Lee-Zhang smoothed shadow bound O(sigma^{-3/2} d^{13/4} log^{5/4} n)

Let $S(n, d, \sigma)$ be the smoothed shadow size: the maximum, over $\bar a_1, \dots, \bar a_n \in \mathbb{R}^d$ of norm at most $1$ and fixed two-dimensional subspaces $W$, of the expected number of edges of $\mathrm{conv}(a_1, \dots, a_n) \cap W$, where the $a_i \sim \mathcal{N}(\bar a_i, \sigma^2 I_d)$ are independent.

**Fixed-plane shadow bound.** For $n \ge d \ge 3$ and $\sigma \le 1/(8d\sqrt{\log n})$,

$$
S(n, d, \sigma) = O\!\left(\sigma^{-3/2} d^{13/4} \log^{5/4} n\right),
$$

improving the dependence on the noise level from $\sigma^{-2}$ to $\sigma^{-3/2}$ in this small-noise range.

**Algorithmic reduction.** The smoothed complexity $\mathrm{SC}$ of the shadow vertex simplex algorithm satisfies $S(n, d, \sigma)/4 \le \mathrm{SC} \le 2\, S\big(n + d, d, \min(\sigma, 1/(\sqrt{d}\,\log d), 1/\sqrt{d\log n})\big) + 4$. Scaling the constraints down to bring the effective noise into the range of the shadow bound costs an additive term independent of $\sigma$, and the resulting simplex method takes

$$
O\!\left(\sigma^{-3/2} d^{13/4} \log^{5/4} n + d^{19/4} \log^2 n\right)
$$

pivot steps; the additive term is needed for noise levels up to $\sigma = 1$. The same analysis gives, for independent $a_i \sim \mathcal{N}(\bar a_i, \sigma^2 I_2)$ with $n > 2$ and $\|\bar a_i\| \le 1$ in the plane, $\mathbb{E}[\mathrm{edges}(\mathrm{conv}(a_1, \dots, a_n))] = O\big(\sqrt{\log n} + \sqrt[4]{\log n}/\sqrt\sigma\big)$. The conference version states the fixed-plane bound with $\log^{7/4} n$.

## Proof sketch

The proof gives a new analysis of the shadow bound, again counting edges of the polar section, but bounding the expected number of short edges through a finer account of how Gaussian noise distributes edge lengths along the section boundary instead of a uniform per-edge length bound. The algorithmic reduction is the two-phase reduction used for the Dadush-Huiberts bound, with the lower inequality due to Borgwardt.

## Depends on

- [Gaussian-smoothed linear programs and smoothed pivot complexity](gaussian-smoothed-linear-programs.md)

## Proof depends on

- [Dadush-Huiberts shadow bound for smoothed unit linear programs](dadush-huiberts-shadow-bound.md)
- [Shadow vertices are bounded by edges of the polar section](shadow-vertices-and-polar-section.md)
- [The shadow vertex pivot rule and the smoothed shadow bound](shadow-vertex-rule-and-shadow-bound.md)

## Sources

- S. Huiberts, Y. T. Lee, X. Zhang, "Upper and Lower Bounds on the Smoothed Complexity of the Simplex Method", STOC (2023), TheoretiCS 4 (2025), arXiv:2211.11860, Section 1 (Theorems 1.1, 1.2 and 1.4, Table 1).
