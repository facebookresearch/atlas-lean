# Sampling colour classes of edge-coloured fractional matchings with negative association

Let $x$ be a fractional matching of $G$, $\varepsilon \in (0, 1)$ and $d \ge 1$. Partition the support of $x$ into classes $G_i = \{e : x_e \in ((1+\varepsilon)^{-i}, (1+\varepsilon)^{-i+1}]\}$, fix a proper edge colouring of each $G_i$, and let $H$ be the union over $i$ of a uniformly random set of colour classes of $G_i$, of size proportional to $d(1+\varepsilon)^{-i}$ times the number of colours (all classes when this exceeds the number of colours). Then for every edge $e$,

$$
\frac{\min\{1, d\,x_e\}}{1 + \varepsilon} \le \Pr[e \in H] \le (1 + \varepsilon)\min\{1, d\,x_e\},
$$

with $\Pr[e \in H] = 1$ when $x_e > 1/d$, and for every vertex $v$ the indicators $\{\mathbf{1}[e \in H]\}_{e \ni v}$ are negatively associated. Hence Chernoff-Hoeffding bounds apply to $\deg_H(v)$, and $H$ is a randomized kernel of size $\tilde O(\mu(G))$ after suitable thresholding.

## Proof sketch

A colour class is a matching, so each edge of $G_i$ lies in exactly one class, and sampling $k$ of the $K$ classes includes it with probability $k/K$, which by the choice of $k$ is within a $1 + \varepsilon$ factor of $\min\{1, d x_e\}$. The classes are sampled without replacement, a permutation distribution, which is negatively associated, and independent sampling across distinct $i$ preserves negative association. Since $v$ has at most one edge per colour class, its incident indicators are monotone functions of disjoint coordinates.

## Depends on

- [Fractional matchings and the fractional matching number](fractional-matching-number.md)
- [Randomized (c, d, epsilon)-kernels for maximum matching](randomized-matching-kernels.md)
- [Proper edge coloring](../../../../../GraphTheory/graph-coloring/part-01/edge-coloring/is-proper-edge-coloring.md)

## Sources

- David Wajc, "Rounding Dynamic Matchings Against an Adaptive Adversary", STOC (2020), arXiv:1911.05545.
