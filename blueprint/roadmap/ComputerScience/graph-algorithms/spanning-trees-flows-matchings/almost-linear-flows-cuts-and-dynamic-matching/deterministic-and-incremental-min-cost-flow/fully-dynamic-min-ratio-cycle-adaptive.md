# Deterministic fully dynamic approximate min-ratio cycles against any adversary

For some $\gamma_{\mathrm{MRC}} = \exp(O(\log^{167/168} m\log\log m))$ there is a deterministic $\gamma_{\mathrm{MRC}}$-approximate dynamic min-ratio cycle data structure that, on any dynamic graph with at most $m$ edges undergoing edge insertions, edge deletions and insertions of isolated vertices, and with no restriction on how updates depend on its outputs:

1. initializes in $m\gamma_{\mathrm{MRC}}$ time and processes each update in amortized $\gamma_{\mathrm{MRC}}$ time;
2. maintains a forest that embeds into $G$ with vertex and edge congestion at most $\gamma_{\mathrm{MRC}}$;
3. after each update reports that no cycle exists when $G$ is a forest, whose only circulation is $\mathbf{0}$, and otherwise outputs a nonzero circulation $\mathbf{c}$ represented by $\gamma_{\mathrm{MRC}}$ forest paths and $\gamma_{\mathrm{MRC}}$ off-tree edges with

$$
\frac{\langle\mathbf{g}, \mathbf{c}\rangle}{\|\mathbf{L}\mathbf{c}\|_1} \le \frac{1}{\gamma_{\mathrm{MRC}}}\cdot\min_{\mathbf{B}^{\top}\mathbf{\Delta} = \mathbf{0},\ \mathbf{\Delta} \ne \mathbf{0}}\frac{\langle\mathbf{g}, \mathbf{\Delta}\rangle}{\|\mathbf{L}\mathbf{\Delta}\|_1}.
$$

## Proof sketch

Dynamize the $\ell_1$-oblivious routing built from sparse neighborhood covers at distance scales $\gamma^i$, maintaining the covers and low-diameter cluster trees with dynamic vertex sparsifiers for shortest paths; this reduces min-ratio cycle to min-ratio tree cycle on $m^{o(1)}$ forests by *An l1 oblivious routing yields an approximate minimum-ratio circulation edge by edge*. The tree-cycle problem is reduced back to min-ratio cycle on a graph smaller by a factor $k$ via portal routing and a dynamic low-recourse spanner that tolerates many insertions, in the spirit of the greedy spanner. Alternating the two reductions over $O(\log_k m)$ levels with $k = \exp(O(\log^{167/168} m\log\log m))$ gives the bound, and every component is deterministic and gradient-oblivious until the final cycle extraction, so no assumption on the adversary is needed.

## Depends on

- [Dynamic graph problems](../../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/dynamic-graph-problems.md)
- [Undirected minimum-ratio cycle problem with gradients and lengths](../almost-linear-flow-interior-point-method/undirected-min-ratio-cycle-problem.md)

## Proof depends on

- [An l1 oblivious routing yields an approximate minimum-ratio circulation edge by edge](l1-oblivious-routing-min-ratio.md)
- [Low stretch preserves a minimum-ratio cycle among fundamental tree cycles](../dynamic-min-ratio-cycle-data-structures/tree-cycles-approximate-min-ratio.md)

## Sources

- Li Chen, Rasmus Kyng, Yang P. Liu, Simon Meierhans, Maximilian Probst Gutenberg, "Almost-Linear Time Algorithms for Incremental Graphs: Cycle Detection, SCCs, s-t Shortest Path, and Minimum-Cost Flow", STOC (2024), arXiv:2311.18295.
- Rasmus Kyng, Simon Meierhans, Maximilian Probst Gutenberg, "A Dynamic Shortest Paths Toolbox: Low-Congestion Vertex Sparsifiers and Their Applications", STOC (2024), arXiv:2311.06402.
- Vaclav Rozhon, Christoph Grunau, Bernhard Haeupler, Goran Zuzic, Jason Li, "Undirected (1+epsilon)-Shortest Paths via Minor-Aggregates: Near-Optimal Deterministic Parallel and Distributed Algorithms", STOC (2022), arXiv:2204.05874.
