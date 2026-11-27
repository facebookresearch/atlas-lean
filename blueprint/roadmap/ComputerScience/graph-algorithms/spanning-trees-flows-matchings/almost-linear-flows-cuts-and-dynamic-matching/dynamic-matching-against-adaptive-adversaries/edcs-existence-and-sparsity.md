# Every graph contains a (beta, beta^-)-EDCS, and it has O(n beta) edges

For every graph $G$ on $n$ vertices and all integers $\beta > \beta^{-} \ge 1$, an $\mathrm{EDCS}(G, \beta, \beta^{-})$ exists and can be found in polynomial time, and every such $H$ has $O(n \beta)$ edges.

## Proof sketch

Start from $H = \emptyset$ and repeatedly fix a violated edge: remove an edge of $H$ violating (P1) or insert an edge of $G \setminus H$ violating (P2). The potential $\Psi(H) = (\beta - \tfrac12)|E_H| - \tfrac12\sum_{v} \deg_H(v)^2$ increases by at least $1/2$ at each fix, using $\deg_H(u) + \deg_H(v) \ge \beta + 1$ for a removal and $\deg_H(u) + \deg_H(v) \le \beta^{-} - 1 \le \beta - 2$ for an insertion, and it is bounded by $O(n\beta^2)$, so the process terminates. For sparsity, (P1) gives every edge of $H$ an endpoint of $H$-degree at most $\beta/2$; charging each edge to such an endpoint charges every vertex at most $\beta/2$ times, so $|E_H| \le n\beta/2$.

## Depends on

- [Edge-degree constrained subgraphs (EDCS)](edge-degree-constrained-subgraph.md)

## Sources

- Sepehr Assadi, Aaron Bernstein, "Towards a Unified Theory of Sparsification for Matching Problems", SOSA (2019), arXiv:1811.02009.
- Aaron Bernstein, Cliff Stein, "Fully Dynamic Matching in Bipartite Graphs", ICALP (2015), arXiv:1506.07076.
