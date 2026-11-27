# Deterministic (c, d, 0)-kernels preserve maximum matching within 2c(1+1/d)

Let $d \ge 1$ be an integer. If $H$ is a deterministic $(c, d, 0)$-kernel of $G$, then

$$
\mu(G) \le 2c\Bigl(1 + \frac{1}{d}\Bigr) \mu(H).
$$

More generally, if $0 \le \varepsilon < 1$ and $H$ is a randomized $(c, d, \varepsilon)$-kernel of $G$ with $c \ge 1/(1 - \varepsilon)$, then $\mathbb{E}[\mu(H)] \ge \mu(G)/(2c(1 + 1/d))$. The restriction $\varepsilon < 1$ is needed: for $\varepsilon \ge 1$ the second kernel condition is vacuous, so the empty subgraph of a single edge is a kernel while $\mu(G) = 1$.

## Proof sketch

Fix a maximum matching $M^\ast$ of $G$ and, for each realization of $H$, define $f_e = 1/d$ for $e \in H \setminus M^\ast$ and $f_{uv} = \max\{1 - (\deg_H(u) + \deg_H(v) - 2)/d, 0\}$ for $uv \in H \cap M^\ast$; the degree bound makes $f$ a fractional matching. With $y_v = \sum_{e \ni v} f_e$, every $uv \in M^\ast \cap H$ has $y_u + y_v \ge 1$, and every $uv \in M^\ast \setminus H$ has $y_u + y_v \ge \max_{w \in \{u, v\}}\deg_H(w)/d$. Split the edges $e = uv$ of $M^\ast$ at exclusion probability $\varepsilon$: if $\Pr[e \notin H] \le \varepsilon$, then $\mathbb{E}[y_u + y_v] \ge 1 - \varepsilon \ge 1/c$; otherwise the kernel property gives $\mathbb{E}[\max_{w \in \{u, v\}}\deg_H(w)/d \mid e \notin H] \ge 1/c$, so $\mathbb{E}[y_u + y_v] \ge \Pr[e \in H] + \Pr[e \notin H]/c \ge 1/c$. Summing over the disjoint edges of $M^\ast$, the expected value of $f$ is at least $\mu(G)/(2c)$. Replacing each edge $e$ by $d f_e$ parallel copies gives a multigraph of maximum degree at most $d$. It is $(d+1)$-edge-colourable: colour the simple graph $H \setminus M^\ast$, of maximum degree at most $d$, with $d + 1$ colours by *Vizing's theorem*, then give the $d f_{uv}$ copies of each $uv \in H \cap M^\ast$ distinct colours unused at $u$ and $v$, of which at least $d + 1 - (\deg_H(u) - 1) - (\deg_H(v) - 1) = d f_{uv} + 1$ remain when $f_{uv} > 0$. So some colour class is a matching of $H$ of size at least $\sum_e f_e/(1 + 1/d)$.

## Depends on

- [Randomized (c, d, epsilon)-kernels for maximum matching](randomized-matching-kernels.md)
- [Fractional matchings and the fractional matching number](fractional-matching-number.md)

## Proof depends on

- [Proper edge coloring](../../../../../GraphTheory/graph-coloring/part-01/edge-coloring/is-proper-edge-coloring.md)
- [Vizing's theorem](../../../../../GraphTheory/graph-coloring/part-01/edge-coloring/vizing.md)

## Sources

- David Wajc, "Rounding Dynamic Matchings Against an Adaptive Adversary", STOC (2020), arXiv:1911.05545.
- Sayan Bhattacharya, Monika Henzinger, Giuseppe F. Italiano, "Deterministic Fully Dynamic Data Structures for Vertex Cover and Matching", SODA (2015), arXiv:1412.1318.
