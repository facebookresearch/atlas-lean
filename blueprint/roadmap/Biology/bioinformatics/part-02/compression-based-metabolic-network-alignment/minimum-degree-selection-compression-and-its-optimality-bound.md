# Minimum-degree selection compression and its optimality bound

**Setting.** A metabolic network is represented as a directed graph $P=(V,E)$ on reactions, with an edge $v_i\to v_j$ iff some output compound of $v_i$ is an input of $v_j$. One *compression level* turns $P^{x-1}$ into $P^x$ by a sequence of steps, each merging two adjacent nodes of $P^{x-1}$ that have not yet been merged at this level into a supernode, until no such pair remains; nodes left unmerged are carried over. After $c$ levels every node of $P^c$ contains between $1$ and $2^c$ reactions. The number of merges performed at one level is the size of the matching formed by the merged pairs in the underlying undirected graph of $P^{x-1}$.

**Minimum-degree selection (MDS).** At each step, the degree of a non-compressed node counts only edges to other non-compressed nodes; MDS picks a non-compressed node $v_a$ of minimum positive degree and merges it with a non-compressed neighbour $v_b$. Let $\mathrm{MDS}(C,\ast)$ and $\mathrm{OPT}(C,\ast)$ denote the number of merges made by MDS and by an optimal compression (maximum number of merges at the level).

**Lemma 1.** If the current state of a connected component has a non-compressed node of degree one, the MDS step is optimal: $\mathrm{OPT}(C_i^x)=1+\mathrm{OPT}(C_{i+1}^x)$.

**Lemma 2.** If the minimum degree is greater than one, the MDS step loses at most one merge: $\mathrm{OPT}(C_i^x)\le 2+\mathrm{OPT}(C_{i+1}^x)$.

**Theorem 1 (optimality bound for MDS).** Let $P$ have connected components $C_1,\dots,C_r$, let $c\ge 1$ be the number of levels, and let $s$ be the number of MDS steps at which no non-compressed node had degree one. Then

1. $\mathrm{OPT}(C^{x-1},\ast^x)\le 2\,\mathrm{MDS}(C^{x-1},\ast^x)$ for each component and each level $x=1,\dots,c$;
2. $\mathrm{OPT}(P,\ast^c)\le s+\mathrm{MDS}(P,\ast^c)$;
3. $\mathrm{OPT}(P,\ast^c)\le\min\{2\,\mathrm{MDS}(P,\ast^c),\;s+\mathrm{MDS}(P,\ast^c)\}$.

## Expansion

One level of compression chooses a set of vertex-disjoint adjacent pairs, i.e. a matching, and stops only when the matching is maximal; so MDS is a greedy maximal matching and part 1 is the classical fact that any maximal matching has at least half the size of a maximum matching. Lemma 1 is the standard leaf argument: some maximum matching uses the unique edge at a degree-one vertex, so taking it costs nothing. When every remaining vertex has degree at least two, merging $v_a$ with $v_b$ can destroy at most the two optimal pairs containing $v_a$ and $v_b$ while contributing one pair, which is Lemma 2; counting such steps gives part 2, and summing part 1 over components and levels gives the factor two in part 3. Bounding the number of reactions per supernode by $2^c$ keeps the refinement subproblems small, which is why matching-based (rather than arbitrary contraction-based) compression is used.

## Sources

- Ay F, Dang M, Kahveci T, "Metabolic network alignment in large scale by network compression" (2012), compression method (Methods, "Minimum degree selection (MDS) method"), Lemma 1, Lemma 2 and Theorem 1 ("Optimality analysis for MDS"), <https://doi.org/10.1186/1471-2105-13-s3-s2>, PMCID PMC3402922.
