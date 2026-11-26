# Fractional matchings and the fractional matching number

A *fractional matching* of a graph $G = (V, E)$ is a vector $x \in \mathbb{R}_{\ge 0}^{E}$ with $\sum_{e \ni v} x_e \le 1$ for every $v \in V$; its value is $\|x\|_1 = \sum_{e} x_e$, and $\nu_f(G)$ is the maximum value. Every matching is a $0/1$ fractional matching, so $\mu(G) \le \nu_f(G)$. Conversely $\nu_f(G) \le \frac{3}{2}\mu(G)$ for every graph, and $\nu_f(G) = \mu(G)$ when $G$ is bipartite (by Kőnig's theorem and LP duality with the fractional vertex cover). Dynamic *rounding* asks to maintain an integral matching of size close to $\|x\|_1$ while $x$ changes under updates.

## Depends on

- [Fully dynamic alpha-approximate maximum matching and its value version](dynamic-approximate-matching-problem.md)

## Sources

- David Wajc, "Rounding Dynamic Matchings Against an Adaptive Adversary", STOC (2020), arXiv:1911.05545.
- Alexander Schrijver, "Combinatorial Optimization: Polyhedra and Efficiency", Springer (2003).
