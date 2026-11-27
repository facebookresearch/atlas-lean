# Maximum-flow oracles and the max-flow call model for cut problems

Let $G = (V, E, w)$ be an undirected graph with $n = |V|$, $m = |E| \ge n - 1$ and integer edge weights $w : E \to \{1, \dots, W\}$, where $W \le n^{O(1)}$. For $S \subseteq V$ write $\partial S$ for the set of edges with exactly one endpoint in $S$ and $w(\partial S) = \sum_{e \in \partial S} w(e)$.

A *maximum-flow oracle* receives an undirected weighted graph $H$ and two disjoint nonempty vertex sets $A, B \subseteq V(H)$ and returns a set $X$ with $A \subseteq X \subseteq V(H) \setminus B$ minimizing $w(\partial_H X)$ (a minimum $(A,B)$-cut, obtained from a maximum flow between the contracted sets $A$ and $B$ by the max-flow min-cut theorem). Let $\mathrm{MF}(n, m)$ denote the running time of the oracle on graphs with $n$ vertices and $m$ edges; it is assumed that $\mathrm{MF}(n,m) \ge m$ and that $\mathrm{MF}$ is superadditive:

$$
\mathrm{MF}(n_1, m_1) + \mathrm{MF}(n_2, m_2) \le \mathrm{MF}(n_1 + n_2, m_1 + m_2).
$$

An algorithm *uses $k$ max-flow calls* if it makes oracle calls on graphs $H_1, \dots, H_r$ that can be grouped into $k$ batches, each batch having at most $O(n)$ vertices and $O(m)$ edges in total, so that the oracle time is $O(k \cdot \mathrm{MF}(n, m))$. With the randomized almost-linear maximum-flow algorithm one may take $\mathrm{MF}(n,m) = m^{1+o(1)}$, correct with probability $1 - n^{-c}$.

## Depends on

- [Source–sink cut](../../../../../GraphTheory/matchings-and-flows/max-flow-min-cut-theorem/is-stcut.md)
- [Cut capacity](../../../../../GraphTheory/matchings-and-flows/max-flow-min-cut-theorem/cut-capacity.md)

## Sources

- Jason Li, Debmalya Panigrahi, "Deterministic Min-cut in Poly-logarithmic Max-flows", FOCS (2020), arXiv:2111.02008.
- Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, "Maximum Flow and Minimum-Cost Flow in Almost-Linear Time", FOCS (2022), arXiv:2203.00671.
