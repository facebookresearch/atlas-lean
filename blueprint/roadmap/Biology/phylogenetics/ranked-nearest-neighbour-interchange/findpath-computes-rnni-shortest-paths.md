# FindPath computes RNNI shortest paths in quadratic time

Let $T$ and $R$ be ranked trees on $n$ leaves in the [unweighted RNNI graph](rnni-graph-of-ranked-phylogenetic-trees.md), and let $[C_1, \dots, C_{n-1}]$ be the cluster representation of $R$. For a leaf set $S$ write $(S)_{T}$ for its most recent common ancestor in $T$, the lowest-ranked node whose cluster contains $S$.

**Algorithm (FindPath).** Set the current tree $T_1 := T$ and start with an empty list of moves. For $k = 1, \dots, n-2$: while the rank $r$ of $(C_k)_{T_1}$ in $T_1$ exceeds $k$, apply to $T_1$, in place, the unique RNNI move that decreases this rank by one (a rank move if the nodes of ranks $r-1$ and $r$ are not adjacent, otherwise the unique NNI move on that edge that lowers the rank of $(C_k)_{T_1}$), and append a description of that move (its type, the ranks involved and, for an NNI move, which subtree is exchanged) to the list. At the end $T_1 = R$, and the list describes the path from $T$ to $R$ move by move.

**Proposition.** FindPath is a correct deterministic algorithm that returns its path as a list of $O(n^2)$ moves in $O(n^2)$ time: at each step the decreasing move exists and is unique. Every cluster shared by $T$ and $R$ is present in every tree on the computed path. Returning the path as a list of trees instead would cost order $n^3$ time on the caterpillar pair below, since each of its order $n^2$ trees has $n$ leaves.

**Theorem.** The path computed by FindPath is a shortest path in $\mathrm{RNNI}(1)$. Hence the RNNI distance, and a shortest path realizing it, can be computed in $O(n^2)$ time.

**Corollary (optimality).** Any algorithm that outputs an RNNI shortest path, as a list of moves, takes $\Omega(n^2)$ time in the worst case: for the caterpillars $T = [\{a_1,a_2\}, \{a_1,a_2,a_3\}, \dots]$ and $R = [\{a_1,a_n\}, \{a_1,a_n,a_{n-1}\}, \dots]$ the shortest path has length $(n-1)(n-2)/2$. The bound is for producing a path; it says nothing about computing the distance alone.

## Depends on

- [RNNI graph of ranked phylogenetic trees](rnni-graph-of-ranked-phylogenetic-trees.md)

## Expansion

The theorem is proved by contradiction: take a pair $T, R$ at minimum distance for which FindPath is not optimal, and compare the first move of a shortest path with the first move of FindPath. A case analysis shows the first move of a shortest path can be replaced by FindPath's move without lengthening the path, contradicting minimality. The quadratic lower bound comes from the output size of a path, since the caterpillar pair needs $\sum_{k=1}^{n-2} k$ moves; it does not bound the time needed to return the length alone. This was the first phylogenetic rearrangement graph shown to admit polynomial-time distance computation; NNI, SPR and TBR distances on unranked trees are NP-hard.

## Sources

- L. Collienne and A. Gavryushkin, "Computing nearest neighbour interchange distances between ranked phylogenetic trees", *Journal of Mathematical Biology* 82 (2021), article 8, <https://doi.org/10.1007/s00285-021-01567-5> (PMC7835203; Proposition 1, Theorem 1 and Corollary 1).
