# Sampling colour classes of edge-coloured fractional matchings with negative association

Let $x$ be a fractional matching of $G$, $\varepsilon \in (0, 1)$, $d \ge 1/\varepsilon$ and $\gamma \ge 1$ an integer, so that the colour counts below are integers. For $i \ge 1$ let $G_i$ consist of the edges with $x_e \in ((1+\varepsilon)^{-i}, (1+\varepsilon)^{-i+1}]$; its maximum degree is below $(1+\varepsilon)^i$. Fix a proper edge colouring of each $G_i$ with $\gamma\lceil(1+\varepsilon)^i\rceil$ colours, let $S_i$ be a uniformly random set of $\min\{\gamma\lceil d(1+\varepsilon)\rceil, \gamma\lceil(1+\varepsilon)^i\rceil\}$ of these colours, drawn without replacement and independently for different $i$, and let $H$ be the union of the colour classes in all the $S_i$. Then for every edge $e$ of the support of $x$,

$$
\frac{\min\{1, d\,x_e\}}{(1 + \varepsilon)^2} \le \Pr[e \in H] \le \Big(1 + \varepsilon + \frac1d\Big)\min\{1, d\,x_e\} \le (1 + 2\varepsilon)\min\{1, d\,x_e\},
$$

with $\Pr[e \in H] = 1$ when $x_e > 1/d$, and with the sharper upper factor $1 + \varepsilon$ when $d(1+\varepsilon)$ is an integer. The extra $1/d$ comes from the ceiling in the number of sampled colours and cannot be dropped in general: for $\varepsilon = 1/2$, $d = 3$, $\gamma = 1$ and $x_e = 2/15$, the edge lies in $G_5$, which has $\lceil 1.5^5 \rceil = 8$ colours, of which $\lceil 4.5 \rceil = 5$ are drawn, so $\Pr[e \in H] = 5/8 > 3/5 = (1+\varepsilon)\,d\,x_e$. Wajc's Lemma 3.2 states the factor $1 + \varepsilon$ for the sampling rule of his Algorithm 1; his proof computes with $\gamma\lceil d\rceil$ sampled colours in the classes with $(1+\varepsilon)^{i-1} \ge d$, where the factor $1+\varepsilon$ is valid. Further, for every vertex $v$ the indicators $\{\mathbf{1}[e \in H]\}_{e \ni v}$ are negatively associated. Hence Chernoff-Hoeffding bounds apply to $\deg_H(v)$. Every colour class is a matching of $G$, so restricting to the $\lceil 2\log_{1+\varepsilon}(n/\varepsilon)\rceil$ classes $G_i$ that carry all but $\varepsilon^2$ of the value of $x$ gives $|E(H)| = O(\varepsilon^{-1}\log(n/\varepsilon)\,\gamma\, d\,\mu(G))$.

## Proof sketch

A colour class is a matching, so each edge of $G_i$ lies in exactly one class, and sampling $k$ of the $K$ classes includes it with probability $\min\{k, K\}/K$; here $k = \gamma\lceil d(1+\varepsilon)\rceil$ and $K = \gamma\lceil(1+\varepsilon)^i\rceil$, and $(1+\varepsilon)^{-i} < x_e \le (1+\varepsilon)^{-i+1}$. If $(1+\varepsilon)^{i-1} < d$, then $K \le k$, so $e$ is always sampled, and $1 \le (1+\varepsilon)\min\{1, d x_e\}$ because $x_e > 1/(d(1+\varepsilon))$; every edge with $x_e > 1/d$ is in this case. If $(1+\varepsilon)^{i-1} \ge d$, then $d x_e \le 1$, the probability is at most $(d(1+\varepsilon) + 1)/(1+\varepsilon)^i < (1 + \varepsilon + 1/d)\,d x_e$, or $(1+\varepsilon)\,d x_e$ when $d(1+\varepsilon)$ is an integer, and at least $\min\{1, d/((1+\varepsilon)^i + 1)\} \ge d x_e/(1+\varepsilon)^2$, using $1 \le \varepsilon (1+\varepsilon)^i$, which follows from $(1+\varepsilon)^{i-1} \ge d \ge 1/\varepsilon$. Finally $1/d \le \varepsilon$. The classes are sampled without replacement, a permutation distribution, which is negatively associated, and independent sampling across distinct $i$ preserves negative association. Since $v$ has at most one edge per colour class, its incident indicators are monotone functions of disjoint coordinates.

## Depends on

- [Fractional matchings and the fractional matching number](fractional-matching-number.md)
- [Randomized (c, d, epsilon)-kernels for maximum matching](randomized-matching-kernels.md)
- [Proper edge coloring](../../../../../GraphTheory/graph-coloring/part-01/edge-coloring/is-proper-edge-coloring.md)

## Sources

- David Wajc, "Rounding Dynamic Matchings Against an Adaptive Adversary", STOC (2020), arXiv:1911.05545, Algorithm 1, Observation 3.1, Lemmas 3.2 and 3.3 and Appendix B.
