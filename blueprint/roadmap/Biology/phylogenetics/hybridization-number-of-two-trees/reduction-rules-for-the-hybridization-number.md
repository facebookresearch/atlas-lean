# Reduction rules for the hybridization number

**Definitions.** A rooted binary phylogenetic $X$-tree has leaf set $X$, a root of degree two and all other internal vertices of degree three. A hybridization network on $X$ is a rooted acyclic digraph with leaf set $X$; its vertices of in-degree at least two are hybridization vertices, and its hybridization number $h(\mathcal H)$ is the number of hybridization vertices. For two rooted binary $X$-trees $S, T$, $h(S,T)$ is the minimum of $h(\mathcal H)$ over networks displaying both. A forest of $S$ is a collection of vertex-disjoint rooted subtrees of $S$ whose leaf sets partition $X$; an **agreement forest** of $S$ and $T$ is a forest of both; it is **acyclic** if the inheritance graph on its components, ordered by ancestry in $S$ and in $T$, has no directed cycle.

**Characterization.** $h(S,T) = m(S,T) - 1$, where $m(S,T)$ is the minimum number of components of an acyclic agreement forest of $S$ and $T$.

**Reduction rules.** Each rule runs in polynomial time and preserves $h$ as stated.
1. *Subtree reduction.* Replace a maximal pendant subtree with at least two leaves that occurs identically in $S$ and $T$ by a single new leaf; then $h(S,T) = h(S',T')$.
2. *Chain reduction.* Replace a maximal common chain of $n \ge 3$ leaves, identical and identically oriented towards the root in both trees, by two new leaves $a, b$ carrying weight $n-2$; then $h(S,T) = h(S',T')$ if some minimum acyclic agreement forest of $S', T'$ keeps $a$ and $b$ in one component, and $h(S,T) = h(S',T') + (n-2)$ otherwise (then $a, b$ are isolated).
3. *Cluster reduction.* If $A$ is a minimal cluster with $|A| \ge 2$ common to $S$ and $T$, let $S_1, T_1$ be the subtrees on $A$ and $S_2, T_2$ the trees obtained by replacing them by a single leaf; then $h(S,T) = h(S_1,T_1) + h(S_2,T_2)$, whatever the two topologies on $A$.

Subtree and chain reduction alone produce a kernel whose size is linear in $h(S,T)$, so computing the hybridization number is fixed-parameter tractable in $h$.

## Expansion

Deleting the edges entering each hybridization vertex of an optimal network leaves an acyclic agreement forest with one more component than the hybridization number, and conversely an acyclic forest can be wired back into a network without circular inheritance, which gives the characterization. A common pendant subtree never needs to be cut, and a long common chain is either kept whole or every leaf in it isolated, which is why the chain can be truncated to two leaves with a weight recording the $n-2$ possibly isolated leaves. The cluster rule is the decomposition that makes exhaustive search practical: an algorithm that applies subtree and chain reductions, then splits at the smallest common cluster, then searches each small piece exhaustively solved real grass-family instances that a direct search could not.

## Sources

- M. Bordewich, S. Linz, K. St John, C. Semple, "A reduction algorithm for computing the hybridization number of two trees", Evolutionary Bioinformatics Online 3:86–98 (2007), Section 2 (definitions, the acyclic agreement forest characterization, and Section 2.1 reduction rules), PMCID PMC2684132.
