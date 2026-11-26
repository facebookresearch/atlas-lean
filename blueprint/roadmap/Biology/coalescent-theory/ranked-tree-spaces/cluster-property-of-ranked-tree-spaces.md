# Cluster property of ranked tree spaces

**Spaces.** A **ranked tree** on leaves $\{a_1, \dots, a_n\}$ is a rooted binary tree whose $n - 1$ internal nodes carry distinct ranks $1, \dots, n-1$ increasing toward the root; it is the discrete shape of a coalescent genealogy. The **RNNI graph** has ranked trees as vertices and an edge for each
- *rank move*: swap the ranks of two internal nodes with ranks $i, i+1$ that are not joined by an edge;
- *NNI move*: a nearest-neighbor interchange on an edge joining nodes of ranks $i$ and $i+1$.

A **discrete coalescent tree** in $\mathrm{DCT}_m$ assigns its internal nodes distinct integer times in $\{1, \dots, m\}$ (leaves at time $0$). Its graph adds *length moves*, changing one node time by $\pm 1$ when the target time is free and the order constraints remain satisfied, and allows rank and NNI moves between nodes at consecutive times. A **cluster** is the leaf set below an internal node.

**Theorem 1 (reduction).** Extending each $T \in \mathrm{DCT}_m$ to a ranked tree $T^r$ on $m + 2$ leaves, by attaching a caterpillar of auxiliary leaves whose internal nodes occupy the unused times, gives $d_{\mathrm{DCT}_m}(T, R) = d_{\mathrm{RNNI}}(T^r, R^r)$ whenever $m$ is at least the maximal root time.

**Theorem 2 (cluster property).** If ranked trees $T$ and $R$ share a cluster $C$, then every shortest RNNI path between them consists of trees that all contain $C$.

**Corollary 1.** $\mathrm{DCT}_m$ has the cluster property.

**Theorem 3 (caterpillar convexity).** Between any two caterpillar trees (every internal node has a leaf child) there is a shortest path, in RNNI and in $\mathrm{DCT}_m$, made entirely of caterpillar trees.

**Theorem 4 and its corollary.** For caterpillar trees the RNNI distance equals the number of transpositions (leaf pairs whose parent ranks are in opposite order in $T$ and $R$, a Kendall-tau count) minus a correction term counting leaves that share a parent, and it is computable in $O(n \log n)$ time.

## Expansion

The algorithm FINDPATH builds, for $i = 1, \dots, n-1$, the cluster of the rank-$i$ node of $R$ inside the current tree by repeatedly lowering the rank of its most recent common ancestor, one RNNI move at a time; it never destroys a cluster common to the two trees (Lemma 1) and produces shortest paths. For Theorem 2, take a minimal counterexample: the first move off $C$ is an NNI that changes only the cluster $C$; comparing FINDPATH from $R$ to $T$ and to its neighbor $T'$ shows that $d(T', R) = d(T, R) + 1$, contradicting that $T'$ lies on a shortest path. This sharply contrasts with the unranked NNI space, which lacks the cluster property and where distance computation is NP-hard; in RNNI shortest paths and distances are polynomial.

## Sources

- L. Collienne, K. Elmes, M. Fischer, D. Bryant, A. Gavryushkin, "Discrete coalescent trees", Journal of Mathematical Biology 83(5) (2021) 60, Lemma 1, Theorems 1-4, Corollary 1, <https://doi.org/10.1007/s00285-021-01685-0>, PMCID PMC8571255.
