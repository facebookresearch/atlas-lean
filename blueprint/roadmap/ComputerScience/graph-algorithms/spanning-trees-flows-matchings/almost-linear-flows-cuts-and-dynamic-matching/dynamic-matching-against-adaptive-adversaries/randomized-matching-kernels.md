# Randomized (c, d, epsilon)-kernels for maximum matching

Let $G = (V, E)$, $c \ge 1$, $d \ge 1$ and $\varepsilon \ge 0$. A *$(c, d, \varepsilon)$-kernel* of $G$ is a random subgraph $H \subseteq G$ such that

1. $\deg_H(v) \le d$ for every $v \in V$, always;
2. for every edge $e \in E$ with $\Pr[e \notin H] > \varepsilon$,

$$
\mathbb{E}\bigl[\max_{v \in e} \deg_H(v) \bigm| e \notin H\bigr] \ge d/c.
$$

When $H$ is deterministic and $\varepsilon = 0$ this is the kernel of Bhattacharya, Henzinger and Italiano: edges missing from $H$ have an endpoint of high $H$-degree. Kernels have $O(nd)$ edges.

## Depends on

- [Fully dynamic alpha-approximate maximum matching and its value version](dynamic-approximate-matching-problem.md)

## Sources

- David Wajc, "Rounding Dynamic Matchings Against an Adaptive Adversary", STOC (2020), arXiv:1911.05545.
- Sayan Bhattacharya, Monika Henzinger, Giuseppe F. Italiano, "Deterministic Fully Dynamic Data Structures for Vertex Cover and Matching", SODA (2015), arXiv:1412.1318.
