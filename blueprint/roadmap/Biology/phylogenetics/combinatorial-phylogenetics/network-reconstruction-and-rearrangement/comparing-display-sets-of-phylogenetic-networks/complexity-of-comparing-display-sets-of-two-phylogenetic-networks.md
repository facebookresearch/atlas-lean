# Complexity of comparing the display sets of two phylogenetic networks

**Setting.** A (rooted, binary) phylogenetic network $\mathcal{N}$ on a taxon set $X$ is a rooted acyclic digraph whose leaves are bijectively labeled by $X$, with tree vertices (indegree 1, outdegree 2) and reticulations (indegree 2, outdegree 1). A phylogenetic $X$-tree $T$ is *displayed* by $\mathcal{N}$ if it can be obtained from a subgraph of $\mathcal{N}$ by deleting one incoming arc of every reticulation, removing unlabeled leaves and suppressing degree-two vertices; the **display set** $T(\mathcal{N})$ is the set of trees displayed. $\mathcal{N}$ is *tree-child* if every non-leaf vertex has a non-reticulation child (equivalently, every vertex is *visible*: some leaf is reachable from the root only through it), *normal* if it is tree-child with no arc parallel to a directed path, and *temporal* if its vertices admit times that strictly increase along tree arcs and agree across the two parents of each reticulation.

**Theorem (common trees).** COMMON-TREE-CONTAINMENT, which asks whether $T(\mathcal{N}) \cap T(\mathcal{N}') \ne \emptyset$ for two networks on $X$, is NP-complete even when both $\mathcal{N}$ and $\mathcal{N}'$ are temporal normal networks. Consequently:

- deciding $T(\mathcal{N}) \cap T(\mathcal{N}') = \emptyset$ for two temporal normal networks is co-NP-complete;
- counting $|T(\mathcal{N}) \cap T(\mathcal{N}')|$ for two temporal normal networks is #P-complete;
- deciding whether two tree-based networks have a common base tree is NP-complete.

**Theorem (containment and equivalence).** DISPLAY-SET-CONTAINMENT ($T(\mathcal{N}_1) \subseteq T(\mathcal{N}_2)$?) and DISPLAY-SET-EQUIVALENCE ($T(\mathcal{N}_1) = T(\mathcal{N}_2)$?) are $\Pi_2^P$-complete, i.e. complete for the second level of the polynomial hierarchy. Containment stays $\Pi_2^P$-complete when $\mathcal{N}_1$ is restricted to temporal tree-child caterpillar networks. Along the way, the $\forall\exists$ versions of directed disjoint connecting paths (and their phylogenetic variant) are shown to be $\Pi_2^P$-complete.

These hardness results contrast with the polynomial-time solvability of display-set equivalence for a normal network and a tree-child network, and with the polynomial-time TREE-CONTAINMENT problem for tree-child networks: comparing two networks is much harder than testing a single tree against one network.

## Expansion

NP-membership of COMMON-TREE-CONTAINMENT is immediate (guess a tree and check containment in each network, which is polynomial for tree-child networks). Hardness is a reduction from a satisfiability problem: each clause becomes a pair of gadgets whose display sets are disjoint unless one of its literals is set true, and variable gadgets enforce consistent truth assignments across the two networks, all built so that both networks remain temporal and normal. For containment, the statement "every tree of $\mathcal{N}_1$ is displayed by $\mathcal{N}_2$" has a natural $\forall\exists$ form (for every choice of reticulation arcs in $\mathcal{N}_1$ there is a choice in $\mathcal{N}_2$); hardness comes from the $\forall\exists$ disjoint-paths problem, with the universally quantified choices encoded by the reticulations of a caterpillar-like network. Equivalence inherits hardness because containment reduces to it.

## Sources

- Janosch Döcker, Simone Linz and Charles Semple, "Displaying trees across two phylogenetic networks", arXiv:1901.06612 (2019), Lemma 2.1, Theorem 3.2, Corollary 3.3, Theorems 4.1, 4.3 and 4.5, Corollaries 4.2, 4.4 and 5.1–5.3, <https://doi.org/10.48550/arXiv.1901.06612>. Published version: Theoretical Computer Science, 796:129-146, 2020, <https://doi.org/10.1016/j.tcs.2019.09.003>.
