# Induced subnetwork of a phylogenetic network

Let $G$ be a connected directed graph. A vertex of outdegree $0$ is a **leaf**; a vertex with indegree at least $2$ is a **reticulation**. $G$ is **rooted** if it has a unique vertex $\rho(G)$ of indegree $0$. In a directed acyclic graph (DAG), $u$ is an ancestor of $v$ if $u = v$ or there is a directed path from $u$ to $v$; $v$ is below $u$ if $u$ is an ancestor of $v$ and $u \ne v$. A vertex of outdegree $1$ is **degenerate** if its indegree is at most $1$ (for $G$ with at least three vertices). $G$ is **binary** if the root has outdegree $2$ and every interior vertex has indegree plus outdegree equal to $3$.

For a nonempty set $X$ of taxa, a **phylogenetic network on $X$** is a rooted DAG $N$ without degenerate vertices whose leaf set is $X$, with root outdegree at least $2$ unless $N$ has exactly two vertices. A network without reticulations is a phylogenetic tree. Two networks on $X$ are **equivalent** if they are isomorphic by a map fixing every leaf.

For nonempty $Y \subseteq X$, the **lowest stable ancestor** $\mathrm{lsa}(Y)$ is the non-leaf vertex lying on all directed paths from $\rho(N)$ to elements of $Y$ such that no vertex below it has this property. $N$ is **recoverable** if $\mathrm{lsa}(X) = \rho(N)$. The **subnetwork induced by $Y$**, $N|_Y$, is obtained by

1. deleting every vertex not on a directed path from $\mathrm{lsa}(Y)$ to some element of $Y$, and
2. repeatedly suppressing degenerate vertices (replacing arcs $(u, v), (v, w)$ through such $v$ by $(u, w)$) and deleting parallel arcs, until a phylogenetic network on $Y$ remains.

Induced subnetworks on three leaves are **trinets**. Two networks $N, N'$ on $X$ are **network-equivalent** if $N|_Y$ and $N'|_Y$ are equivalent for every nonempty proper subset $Y \subsetneq X$.

**Properties.**

- $N|_X = N$ if and only if $N$ is recoverable, and every induced subnetwork $N|_Y$ is recoverable.
- (Lemma) If $N_1$ and $N_2$ are recoverable networks on $X$ and are equivalent, they are network-equivalent.

Suppressing degenerate vertices reflects what data can show: the number of degree-two vertices along a lineage cannot be recovered from sequences, so a subnetwork should record only branching and reticulation structure.

## Expansion

The lemma is immediate from the definitions: a leaf-fixing isomorphism $N_1 \to N_2$ maps directed paths to directed paths, hence maps $\mathrm{lsa}(Y)$ in $N_1$ to $\mathrm{lsa}(Y)$ in $N_2$ and the vertices kept in step 1 onto each other; suppressions and deletions of parallel arcs commute with the isomorphism, so $N_1|_Y$ and $N_2|_Y$ are equivalent for every $Y$. Recoverability of $N|_Y$ holds because, after step 1, $\mathrm{lsa}(Y)$ is the root and still the lowest vertex on all root-to-$Y$ paths. The converse of the lemma, that network-equivalence forces equivalence, is the encoding question; it fails in general.

## Sources

- K. T. Huber, L. van Iersel, V. Moulton and T. Wu, "How much information is needed to infer reticulate evolutionary histories?", Systematic Biology 64(1) (2015), 102–111, Mathematical Definitions (Digraphs; Phylogenetic Trees and Networks; Lemma 1), <https://doi.org/10.1093/sysbio/syu076> (PMC4265143).
- The subnetwork definition follows K. T. Huber and V. Moulton, "Encoding and constructing 1-nested phylogenetic networks with trinets", Algorithmica (2012).
