# Branch-and-bound maximal biclique enumeration

**Definitions.** Let $G = (U \cup V, E)$ be a bipartite graph with $|U| \ge |V|$. A biclique is a pair $(L, R)$ with $L \subseteq U$, $R \subseteq V$ and every vertex of $L$ adjacent to every vertex of $R$; it is maximal if no vertex can be added to either side. For $R \subseteq V$ write $\Gamma(R) = \{u \in U : (u,v) \in E\ \forall v \in R\}$ for the common neighbourhood.

**Search state.** The algorithm (MBEA) explores tuples $\langle L, R, P, Q\rangle$ with $L = \Gamma(R)$, candidate set $P \subseteq V$ and former-candidate set $Q \subseteq V$ such that $P, Q, R$ are pairwise disjoint and $P \cup Q = \{v \in V \setminus R : v \text{ has a neighbour in } L\}$. It starts from $\langle U, \emptyset, V, \emptyset\rangle$; a branch picks $x \in P$, sets $R' = R \cup \{x\}$, $L' = L \cap N(x)$, filters $P$ and $Q$ to vertices with neighbours in $L'$, and afterwards moves $x$ from $P$ to $Q$.

**Observations.**
1. $(L, R)$ is always a biclique, and because $L = \Gamma(R)$ it is maximal if and only if no vertex of $V \setminus R$ is adjacent to every vertex of $L$.
2. If $S = \{v \in P : v \text{ adjacent to all of } L\}$, then $(L, R \cup S)$ is a maximal biclique provided no vertex of $Q$ is adjacent to all of $L$.
3. (Pruning.) If $T = \{v \in Q : v \text{ adjacent to all of } L\}$ is non-empty, then for every $L' \subseteq L$ and $S' \subseteq P$, $(L', R \cup S')$ is not a maximal biclique, so the whole subtree below the current node can be discarded.

**Correctness.** Every maximal biclique of $G$ is output exactly once: it is reached by adding the vertices of its $V$-side in the order they are selected, and the former-candidate set $Q$ blocks every other order.

## Expansion

Working only on the smaller side $V$ and recomputing $L$ as a common neighbourhood keeps the state small, and the role of $Q$ is the same as the excluded set in Bron–Kerbosch clique enumeration: a vertex already explored that still dominates the current $L$ certifies that everything below has been or will be produced from an earlier branch. Moving all of $S$ into $R$ at once removes dominated candidates without branching on them. A refinement (iMBEA) selects candidates in increasing order of common-neighbourhood size and strengthens the pruning; both scale to bipartite graphs with tens of thousands of vertices from gene–gene-set association data, where consensus-style methods that must keep all bicliques in memory fail.

## Sources

- Y. Zhang, C. A. Phillips, G. L. Rogers, E. J. Baker, E. J. Chesler, M. A. Langston, "On finding bicliques in bipartite graphs: a novel algorithm and its application to the integration of diverse biological data types", BMC Bioinformatics 15:110 (2014), Observations 1–4 and Algorithm MBEA, <https://doi.org/10.1186/1471-2105-15-110>, PMCID PMC4038116.
