# Diameter and radius of ranked tree spaces

Let RNNI be the graph of ranked trees on $n$ leaves under rank and NNI moves, and $\mathrm{DCT}_m$ the graph of discrete coalescent trees with internal-node times in $\{1, \dots, m\}$ under length, rank and NNI moves (see the cluster property of ranked tree spaces).

**Theorem 5.** The diameter of RNNI is

$$\max_{T, R} d_{\mathrm{RNNI}}(T, R) = \frac{(n-1)(n-2)}{2},$$

attained by the two opposite caterpillars $[\{a_1,a_2\}, \{a_1,a_2,a_3\}, \dots]$ and $[\{a_n, a_{n-1}\}, \{a_n,a_{n-1},a_{n-2}\}, \dots]$.

**Theorem 6.** The diameter of $\mathrm{DCT}_m$ is

$$\frac{(n-1)(n-2)}{2} + (m - n + 1)(n - 1).$$

**Theorem 7.** The radius of RNNI equals its diameter: every ranked tree has a caterpillar tree at distance $(n-1)(n-2)/2$. In contrast, the radius of $\mathrm{DCT}_m$ does not equal its diameter in general (an explicit counterexample exists).

**Consequence.** Computing shortest paths takes $\Theta(n^2)$ moves in the worst case in RNNI and $\Theta(nm)$ in $\mathrm{DCT}_m$, matched by the FINDPATH and FINDPATH$^+$ algorithms.

## Depends on

- [Cluster property of ranked tree spaces](cluster-property-of-ranked-tree-spaces.md)

## Expansion

For the upper bound, iteration $i$ of FINDPATH lowers the rank of the most recent common ancestor of one cluster of $R$ from at most $n - 1$ down to $i$, one move at a time, and the iterations together cost at most $\sum_i (n - 1 - i)$ moves, giving $(n-1)(n-2)/2$; the opposite caterpillars show the bound is tight. In $\mathrm{DCT}_m$ the extra term counts length moves: each of the $n - 1$ internal nodes may need to travel across the $m - n + 1$ free time slots. The radius statement is proved by induction on $n$: delete one leaf of the bottom cherry of $T$, take a farthest caterpillar for the smaller tree, and reattach the deleted leaf at the top of that caterpillar; this raises the distance by $n - 1$, from $(n-1)(n-2)/2$ to $n(n-1)/2$, the diameter for $n + 1$ leaves.

## Sources

- L. Collienne, K. Elmes, M. Fischer, D. Bryant, A. Gavryushkin, "Discrete coalescent trees", Journal of Mathematical Biology 83(5) (2021) 60, Theorems 5-7 and Section on diameter and radius, <https://doi.org/10.1007/s00285-021-01685-0>, PMCID PMC8571255.
