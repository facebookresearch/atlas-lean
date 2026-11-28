# Hierarchy-preserving partial order on rooted phylogenetic trees

**Setting.** Let $RP(X)$ be the set of rooted phylogenetic trees on a finite leaf set $X$, $|X|=n$, and let $H(T)$ be the hierarchy (set of clusters) of $T$: it contains $X$ and all singletons, and any two clusters are disjoint or nested. A map $\delta:H(T)\to H(T')$ is *hierarchy-preserving* if it is the identity on singletons and, for all clusters $A,B$ of $T$,

1. (enveloping) $A\subseteq\delta(A)$, and
2. (subset-preserving) $A\subsetneq B$ implies $\delta(A)\subsetneq\delta(B)$.

Write $T\le_{\rm HP}T'$ if such a map exists. For a cluster $D$ of $T$ and inclusion-maximal subclusters $A_1,\dots,A_m$ of $D$ ($m\ge2$) whose union is not $D$, $T^D_{A_1\cup\dots\cup A_m}$ is the tree obtained by deleting the non-singleton $A_i$ and adding the cluster $A_1\cup\dots\cup A_m$.

**Theorem.**

1. If a hierarchy-preserving map $T\to T'$ exists, there is a unique maximal one (pointwise largest images).
2. $\le_{\rm HP}$ is a partial order on $RP(X)$.
3. It refines the classical refinement order: if every cluster of $T$ is a cluster of $T'$, then $T\le_{\rm HP}T'$.
4. The $\le_{\rm HP}$-maximal elements are exactly the binary trees, and the star tree is the minimum. In particular two distinct binary trees are never comparable: a hierarchy-preserving map between binary trees forces them to be equal.
5. If $T\le_{\rm HP}T'$ with maximal map $\delta$, and $A,B,C$ are inclusion-maximal subclusters of some cluster $D$ with $\delta(A)=\delta(B)\supseteq A\cup B\cup C$, then $T<_{\rm HP}T^D_{A\cup B}<_{\rm HP}T'$.

## Expansion

A hierarchy-preserving map witnesses that $T'$ resolves the nesting pattern of $T$: each cluster of $T$ sits inside a cluster of $T'$, and strict nestings are kept strict. Antisymmetry follows because enveloping maps in both directions force equal cluster sizes level by level. Distinct binary trees are maximal, hence incomparable; but any two trees, binary ones included, are joined by a path in the **undirected** Hasse diagram, for example down to the star tree (the minimum) and back up. This is why the induced Hasse diagram gives a connected and local tree space.

## Sources

- Michael Hendriksen and Andrew Francis, "A partial order and cluster-similarity metric on rooted phylogenetic trees", arXiv:1906.02411 (2019), Section 2, Definitions 2.1–2.3 and 2.8, Theorems 2.5, 2.7 and 2.11, Propositions 2.12 and 2.14, <https://doi.org/10.48550/arXiv.1906.02411>.
