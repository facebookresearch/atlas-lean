# RNNI graph of ranked phylogenetic trees

A **ranked phylogenetic tree** on $n$ leaves is a rooted binary tree whose leaves are labelled bijectively by $\{a_1, \dots, a_n\}$ and whose $n-1$ internal nodes are labelled bijectively by ranks $\{1, \dots, n-1\}$ so that every child has strictly smaller rank than its parent (leaves have rank $0$). Two such trees are identical if an isomorphism preserves edges, leaf labels and ranks. There are

$$\frac{(n-1)!\, n!}{2^{n-1}}$$

ranked trees on $n$ leaves. A tree is determined by its **cluster representation** $[C_1, \dots, C_{n-1}]$, where $C_t$ is the set of leaves below the internal node of rank $t$.

**Definition (RNNI($\rho$) graph).** For a real $\rho \ge 0$, the vertices of $\mathrm{RNNI}(\rho)$ are the ranked trees on $n$ leaves, and two trees are adjacent when one is obtained from the other by

1. a **rank move**, exchanging the ranks of the internal nodes of ranks $t$ and $t+1$ when these two nodes are not joined by an edge, of weight $\rho$; or
2. an **NNI move** on an edge joining nodes of consecutive ranks $t, t+1$: trees $T$ and $R$ are joined when contracting such an edge in each gives the same non-binary tree, of weight $1$.

The RNNI distance between two trees is the minimum total weight of a path joining them; $\mathrm{RNNI}(1)$ is the unweighted RNNI graph, which is connected.

## Expansion

Ranked trees record the temporal order of internal events (speciations, transmissions, metastatic seeding), so a tree metric for them must penalize both topological and ordering disagreements; $\rho$ sets the relative cost of an ordering conflict. When $\rho = 0$, trees with the same topology but different rankings are at distance $0$ and the graph defines only a pseudometric. The count of ranked trees is the number of ranked labelled histories: build the tree bottom-up, choosing at each of the $n-1$ merge steps one of $\binom{k}{2}$ pairs among the $k$ current lineages.

## Sources

- L. Collienne and A. Gavryushkin, "Computing nearest neighbour interchange distances between ranked phylogenetic trees", *Journal of Mathematical Biology* 82 (2021), article 8, <https://doi.org/10.1007/s00285-021-01567-5> (PMC7835203; section "Definitions and background results").
