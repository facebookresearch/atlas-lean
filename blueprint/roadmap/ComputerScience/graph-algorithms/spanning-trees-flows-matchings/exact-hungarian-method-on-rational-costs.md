# An exact implementation of the Hungarian method on rational costs

Consider the following implementation for an $n \times n$ cost matrix $w$ with rational (in particular, integer) entries, working with exact rational arithmetic. If $n = 0$ it returns the empty assignment with empty potentials. Otherwise its state is a partial matching $M$ of rows to columns and rational potentials $u, v$; it starts from $M = \emptyset$, $u_i = \min_j w_{ij}$ and $v = 0$. Each of $n$ phases works in the residual graph of the current state: an edge from row $i$ to column $j$ of length $w_{ij} - u_i - v_j$ for each pair not in $M$, and an edge from column $j$ to row $i$ of length $0$ for each pair in $M$. It computes the shortest distance $d$ from the set of unmatched rows to every vertex (all vertices are reachable before the last phase, since the cost matrix is complete), picks an unmatched column $j^*$ of minimum distance, augments $M$ along a shortest simple path from an unmatched row to $j^*$, and sets $u'_i = u_i - d(\text{row } i)$ and $v'_j = v_j + d(\text{column } j)$, all distances taken in the residual graph before augmentation. Then: (1) after every phase $u_i + v_j \le w_{ij}$ for all $i, j$, with equality on $M$, and $|M|$ has grown by one; in particular $d(\text{row } i) = d(\text{column } j)$ for each matched pair before augmentation, and every forward edge of the augmenting path becomes tight; (2) after $n$ phases $M$ is a permutation $\sigma$, and the exact check of $u_i + v_j \le w_{ij}$ for all pairs and of $u_i + v_{\sigma(i)} = w_{i\sigma(i)}$ for all rows, $n^2 + n$ rational comparisons, succeeds; (3) for any permutation $\sigma$ and rational $u, v$ passing that check, $\sigma$ minimizes $\sum_i w_{i\tau(i)}$ over all permutations $\tau$ when the costs are read as real numbers (the check alone does not verify that $\sigma$ is a permutation: with $w = \begin{pmatrix} 0 & 1 \\ 0 & 1 \end{pmatrix}$, $u = v = 0$, the map sending both rows to the first column passes every comparison); (4) the implementation performs $O(n^3)$ rational additions, subtractions and comparisons in total.

## Proof depends on

- [Dual certificate for the assignment problem](dual-certificate-for-the-assignment-problem.md): clause (3): the certificate for real costs.
- [Correctness of the Hungarian algorithm](hungarian-algorithm.md): correctness of the shortest-augmenting-path method.

## Expansion

A sound expansion specifies the following prerequisites and links their statements.

- The potential update by shortest distances keeps all residual lengths nonnegative, makes $d(\text{row } i) = d(\text{column } j)$ on matched pairs and makes every forward edge of a shortest augmenting path tight (clause (1)).
- Dijkstra's method on a digraph with $O(n)$ vertices, nonnegative lengths and dense adjacency in $O(n^2)$ additions and comparisons (clause (4)).

## Sources

- A. Schrijver, *A Course in Combinatorial Optimization*, lecture notes, CWI and University of Amsterdam, 2017, <https://homepages.cwi.nl/~lex/files/dict.pdf>, §3.5, Theorem 3.6 and the remark after it (potentials and Dijkstra)
