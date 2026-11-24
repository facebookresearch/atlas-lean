# Greedy superstring approximation and hardness of the shortest superstring

For a finite set $S$ of strings over a finite alphabet, no one a substring of another, let $\mathrm{OPT}(S)$ be the length of a shortest common superstring. Blum, Jiang, Li, Tromp and Yannakakis (1994) prove four statements: the greedy algorithm GREEDY, which repeatedly merges the two strings with maximum overlap, produces a superstring of length at most $4\,\mathrm{OPT}(S)$ (Theorem 12); the variant MGREEDY also achieves $4\,\mathrm{OPT}(S)$, because it constructs an optimal cycle cover of the overlap graph (Theorem 10) and concatenating the cycles of an optimal cover costs at most $4\,\mathrm{OPT}(S)$ (Theorem 8); TGREEDY produces a superstring of length at most $3\,\mathrm{OPT}(S)$ (Theorem 11); and the shortest superstring problem is MAX SNP-hard (Theorem 18), by reduction from the traveling salesman problem with distances $1$ and $2$.

## Expansion

1. Definitions: overlaps, prefixes and the distance (prefix) graph, cycle covers, and the reduction to substring-free sets.
2. Theorem 8: the lower bound $\mathrm{CYC}(G_S) \le \mathrm{OPT}(S)$ and the bound for concatenating cycles, using the overlap lemma for strings in different cycles.
3. Theorem 10: the greedy choice of edges by overlap yields an optimal assignment for these graphs (the Monge property; compare Hoffman 1963).
4. Theorems 11 and 12: the bounds for TGREEDY and GREEDY.
5. Theorem 18: the MAX SNP-hardness reduction.

## Sources

- A. Blum, T. Jiang, M. Li, J. Tromp and M. Yannakakis, Linear approximation of shortest superstrings, J. ACM 41 (1994), 630–647, Theorems 8, 10, 11, 12 and 18. <https://doi.org/10.1145/179812.179818>
