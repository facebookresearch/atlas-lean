# Deterministic (c, d, 0)-kernels preserve maximum matching within 2c(1+1/d)

Let $d \ge 1$ be an integer. If $H$ is a deterministic $(c, d, 0)$-kernel of $G$, then

$$
\mu(G) \le 2c\Bigl(1 + \frac{1}{d}\Bigr) \mu(H).
$$

More generally, if $H$ is a randomized $(c, d, \varepsilon)$-kernel of $G$ with $c \ge 1/(1 - \varepsilon)$, then $\mathbb{E}[\mu(H)] \ge \mu(G)/(2c(1 + 1/d))$.

## Proof sketch

Fix a maximum matching $M^\ast$ of $G$ and, for each realization of $H$, define $f_e = 1/d$ for $e \in H \setminus M^\ast$ and $f_{uv} = \max\{1 - (\deg_H(u) + \deg_H(v) - 2)/d, 0\}$ for $uv \in H \cap M^\ast$; the degree bound makes $f$ a fractional matching. With $y_v = \sum_{e \ni v} f_e$, every $uv \in M^\ast \cap H$ has $y_u + y_v \ge 1$, and every $uv \in M^\ast \setminus H$ has $y_u + y_v \ge \max_{v \in e}\deg_H(v)/d$, whose conditional expectation is at least $1/c$ by the kernel property; so the expected value of $f$ is at least $\mu(G)/(2c)$. Replacing each edge $e$ by $d f_e$ parallel copies gives a multigraph of maximum degree at most $d$ that, by Vizing's theorem and a recolouring of the copies of $M^\ast$-edges, is $(d+1)$-edge-colourable, so some colour class is a matching of $H$ of size at least $\sum_e f_e/(1 + 1/d)$.

## Depends on

- [Randomized (c, d, epsilon)-kernels for maximum matching](randomized-matching-kernels.md)
- [Fractional matchings and the fractional matching number](fractional-matching-number.md)

## Proof depends on

- [Proper edge coloring](../../../../../GraphTheory/graph-coloring/part-01/edge-coloring/is-proper-edge-coloring.md)

## Sources

- David Wajc, "Rounding Dynamic Matchings Against an Adaptive Adversary", STOC (2020), arXiv:1911.05545.
- Sayan Bhattacharya, Monika Henzinger, Giuseppe F. Italiano, "Deterministic Fully Dynamic Data Structures for Vertex Cover and Matching", SODA (2015), arXiv:1412.1318.
