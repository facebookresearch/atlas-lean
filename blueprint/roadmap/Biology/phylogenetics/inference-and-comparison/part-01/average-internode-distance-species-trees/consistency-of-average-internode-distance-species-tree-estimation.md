# Consistency of average internode distance species-tree estimation

**Setting.** Let $\mathcal G$ be a collection of $k$ unrooted gene trees, each on a subset of $n$ species, and let $S$ be a species tree on the $n$ species. For a gene tree $G$ and taxa $u,v$ of $G$, let $P_G(u,v)$ be the path between their leaves and $d_G(u,v)=|P_G(u,v)|$ its number of edges. Let $\mathcal G_{u,v}$ be the gene trees containing both $u$ and $v$. The *average intertaxon (internode) distance matrix* is

$$\bar d(u,v)=\frac{1}{|\mathcal G_{u,v}|}\sum_{G\in\mathcal G_{u,v}}d_G(u,v).$$

The ASTRID method returns the tree found by a balanced minimum evolution (BME) local search (greedy start, then NNI or SPR moves to a local optimum) on $\bar d$. Weighted variants replace each edge count by a per-edge weight $w(e)\ge 0$, namely branch support ($d_G(u,v)=\sum_{e\in P_G(u,v)}s(e)$) or branch length.

**Theorem 1 (statistical consistency).** Let the gene trees be on all $n$ species and generated independently under the multispecies coalescent (MSC) on $S$. As $k\to\infty$, $\bar d$ converges almost surely to a matrix that is additive on the unrooted topology of $S$. Because the BME local search has a positive safety radius (there is $\epsilon>0$ such that any input $d$ with $\|d-D\|_\infty<\epsilon$ for an additive $D$ on $T$ returns the unrooted topology of $T$), ASTRID run to a local optimum is statistically consistent for the unrooted species-tree topology. This needs complete gene trees: under the i.i.d. model of missing data, in which every pair of species still co-occurs in a positive fraction of gene trees, ASTRID is not statistically consistent.

**Theorem 2 (running time).** The weighted average intertaxon distance matrix can be computed in $O(kn^2)$ time, and BME local search with $p$ NNI or SPR moves on it takes $O(pn^2)$ time, so the total time is $O((k+p)n^2)$.

## Depends on

- [The multispecies coalescent](../../../../coalescent-theory/multispecies-coalescent/gene-tree-prob.md)

## Expansion

Under the MSC the gene trees on all $n$ species are i.i.d., so by the strong law of large numbers $\bar d(u,v)$ converges to $\mathbb E[d_G(u,v)]$. For any pair $u,v$ the expected number of edges between them in a random gene tree decomposes as a sum of contributions from the species-tree branches separating $u$ and $v$ plus pendant terms, which is an additive matrix on the unrooted species tree (the argument originally given for the node-count version used by NJst; counting edges instead of nodes shifts every off-diagonal entry by one and preserves additivity). Consistency then follows from the safety radius: eventually $\bar d$ is within $\epsilon$ of the limiting additive matrix. For Theorem 2, assigning the weights to edges and computing all pairwise path sums by a traversal from each leaf costs $O(n^2)$ per gene tree.

## Sources

- Liu B, Warnow T, "Weighted ASTRID: fast and accurate species trees from weighted internode distances", Algorithms Mol Biol 2023 Jul 19;18:6, Theorems 1 and 2, the definitions of wASTRID-s and wASTRID-pl, and the Discussion on missing data (ASTRID is not consistent under the i.i.d. model, citing Rhodes, Nute and Warnow 2020), <https://doi.org/10.1186/s13015-023-00230-6>, PMCID PMC10355063.
