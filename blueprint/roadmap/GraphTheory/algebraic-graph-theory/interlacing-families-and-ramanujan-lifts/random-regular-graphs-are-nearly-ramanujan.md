# Friedman: random regular graphs are nearly Ramanujan

For every $d \ge 3$ and $\varepsilon > 0$, a uniformly random $d$-regular graph on $n$ vertices satisfies $\max_{i \ge 2}|\lambda_i| \le 2\sqrt{d-1} + \varepsilon$ with probability $1 - o(1)$ as $n \to \infty$ (Alon's second eigenvalue conjecture). More recently Huang, McKenzie and Yau showed that the fluctuations of the extreme nontrivial eigenvalues around $2\sqrt{d-1}$ follow Tracy-Widom statistics at scale $n^{-2/3}$, implying that a constant fraction (about $69\%$) of large random regular graphs are exactly Ramanujan.

## Proof sketch

Friedman uses the trace method with a refined count of non-backtracking closed walks, isolating "tangles" (small dense subgraphs) that produce the only obstruction and showing they occur with vanishing probability. The edge universality result compares the random regular graph with Gaussian orthogonal ensemble statistics through a Green function analysis of the non-backtracking operator.

## Depends on

- [Ramanujan graphs and bipartite Ramanujan graphs](ramanujan-graphs-and-bipartite-ramanujan-graphs.md)
- [Alon-Boppana bound](../../graph-families-and-operations/expander-graphs/alon-boppana.md)

## Proof depends on

- [Ramanujan graphs and bipartite Ramanujan graphs](ramanujan-graphs-and-bipartite-ramanujan-graphs.md)
- [Alon-Boppana bound](../../graph-families-and-operations/expander-graphs/alon-boppana.md)

## Sources

- Joel Friedman, "A proof of Alon's second eigenvalue conjecture and related problems", Memoirs of the AMS 195(910) (2008).
- Jiaoyang Huang, Theo McKenzie, Horng-Tzer Yau, "Ramanujan property and edge universality of random regular graphs", arXiv:2412.20263 (2024).
