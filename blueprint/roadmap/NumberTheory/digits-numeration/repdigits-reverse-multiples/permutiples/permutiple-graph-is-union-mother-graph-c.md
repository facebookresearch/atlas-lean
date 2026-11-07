# Edges of a permutiple's graph lie on cycles of the mother graph

Let $n \ge 1$, $b$ and $k$
be natural numbers, let $\sigma$ be a permutation of $\{0, \dots, k\}$ and let
$(d_k, \dots, d_0)_b$ be an $(n, b, \sigma)$-permutiple, that is, $d_i < b$ for all $i$ and
$(d_k, \dots, d_0)_b = n \cdot (d_{\sigma(k)}, \dots, d_{\sigma(0)})_b$. Its graph has the edges
$(d_i, d_{\sigma(i)})$ for $0 \le i \le k$. Then for every $0 \le j \le k$, the pair
$(d_j, d_{\sigma(j)})$ is an edge of the $(n, b)$-mother graph, and $d_j$ is reachable from
$d_{\sigma(j)}$ along edges of the graph of the permutiple (in zero steps when they are equal),
so the edge $(d_j, d_{\sigma(j)})$ lies on a directed cycle of that graph.

## Sources

- Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*, INTEGERS 25 (2025), Article A111, Theorem 4, quoting Holt, *Finding Permutiples of a Known Base and Multiplier*.
