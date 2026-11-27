# Sampling colour classes of edge-coloured fractional matchings with negative association

Let $x$ be a fractional matching of $G$, $\varepsilon \in (0, 1)$, $d \ge 1/\varepsilon$ and $\gamma \ge 1$. For $i \ge 1$ let $G_i$ consist of the edges with $x_e \in ((1+\varepsilon)^{-i}, (1+\varepsilon)^{-i+1}]$; its maximum degree is below $(1+\varepsilon)^i$. Fix a proper edge colouring of each $G_i$ with $\gamma\lceil(1+\varepsilon)^i\rceil$ colours, let $S_i$ be a uniformly random set of $\min\{\gamma\lceil d(1+\varepsilon)\rceil, \gamma\lceil(1+\varepsilon)^i\rceil\}$ of these colours, drawn without replacement and independently for different $i$, and let $H$ be the union of the colour classes in all the $S_i$. Then for every edge $e$ of the support of $x$,

$$
\frac{\min\{1, d\,x_e\}}{(1 + \varepsilon)^2} \le \Pr[e \in H] \le (1 + \varepsilon)\min\{1, d\,x_e\},
$$

with $\Pr[e \in H] = 1$ when $x_e > 1/d$, and for every vertex $v$ the indicators $\{\mathbf{1}[e \in H]\}_{e \ni v}$ are negatively associated. Hence Chernoff-Hoeffding bounds apply to $\deg_H(v)$. Every colour class is a matching of $G$, so restricting to the $\lceil 2\log_{1+\varepsilon}(n/\varepsilon)\rceil$ classes $G_i$ that carry all but $\varepsilon^2$ of the value of $x$ gives $|E(H)| = O(\varepsilon^{-1}\log(n/\varepsilon)\,\gamma\, d\,\mu(G))$.

## Proof sketch

A colour class is a matching, so each edge of $G_i$ lies in exactly one class, and sampling $k$ of the $K$ classes includes it with probability $k/K$, which by the choice of $k$ and the rounding in the colour counts is within the stated factors of $\min\{1, d x_e\}$. The classes are sampled without replacement, a permutation distribution, which is negatively associated, and independent sampling across distinct $i$ preserves negative association. Since $v$ has at most one edge per colour class, its incident indicators are monotone functions of disjoint coordinates.

## Depends on

- [Fractional matchings and the fractional matching number](fractional-matching-number.md)
- [Randomized (c, d, epsilon)-kernels for maximum matching](randomized-matching-kernels.md)
- [Proper edge coloring](../../../../../GraphTheory/graph-coloring/part-01/edge-coloring/is-proper-edge-coloring.md)

## Sources

- David Wajc, "Rounding Dynamic Matchings Against an Adaptive Adversary", STOC (2020), arXiv:1911.05545.
