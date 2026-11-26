# Connectivity and diameters of tree-based and level-k unrooted network spaces

**Setting.** Unrooted binary proper phylogenetic networks on $X=\{1,\dots,n\}$, reticulation number $r=|E|-(|V|-1)$, and the moves NNI, PR (prune and regraft, generalizing SPR) and TBR, each with a version that keeps the tier ($^0$), adds an edge ($^+$) or removes an edge ($^-$). A network is *tree-based* with base tree $T$ if a subdivision of $T$ is a spanning tree of it; it is *level-$k$* if every blob (nontrivial 2-connected component) can be made acyclic by deleting at most $k$ edges. A subclass is *connected* under a move if any two members are joined by a sequence of moves staying in the subclass, and *isometric* if its intrinsic distance equals the distance in the full space.

**Theorem.**

1. *(Tiers.)* Tier $r$ is connected under NNI with diameter $\Theta(m\log m)$, $m=n+r$; under PR with diameter $\Theta(n+r)$ and at most $n+2r$; under TBR with diameter $\Theta(n+r)$ and at most $n-3-\lfloor(\sqrt{n-2}-1)/2\rfloor+r$.
2. *(Fixed base tree.)* For a tree $T$, the tree-based networks with base tree $T$ in tier $r$ are connected under TBR with diameter between $\lceil r/3\rceil$ and $r$, under PR with diameter between $\lceil r/2\rceil$ and $2r$, and under NNI with diameter $O(r(n+r))$.
3. *(All tree-based networks.)* The tree-based networks with base tree $T$, the tree-based networks of tier $r$, and all tree-based networks are each connected under TBR, PR and NNI; the tier-$r$ tree-based space has diameter $\Theta(n+r)$ under TBR and PR and $O(n\log n+r(n+r))$ under NNI.
4. *(Level-$k$.)* For $k\ge1$, level-$k$ networks are connected under TBR and PR when $n\ge2$ and under NNI when $n\ge3$, with unbounded diameter.
5. *(Non-isometry.)* For $n\ge6$ the tree-based networks are not an isometric subgraph of all networks under TBR or PR; for $n\ge5$ and large enough $k$ the same holds for level-$k$ networks; for $n\ge5$ tier $r$ is not isometric under NNI.

## Expansion

Connectivity is proved by steering every network to a canonical one. In a tier, any network is first made tree-based on a displayed tree, then its extra edges are swept along the base tree into a *handcuffed* configuration on leaves $1$ and $2$, and finally the base tree is sorted into a caterpillar; counting NNI moves at each stage gives the $O(m\log m)$ upper bound, matched by a counting lower bound. For level-$k$ networks one builds a $k$-burl (nested parallel edges) on the edge at leaf $1$, deletes all other blobs using the displayed-tree reduction, and then moves the underlying tree. Non-isometry is shown by explicit pairs at distance two whose only short connecting path passes through a network outside the class, for example a network containing a Petersen-graph blob that loses its Hamiltonian path, and hence tree-basedness, when two pendant edges become adjacent.

## Sources

- R. Janssen, J. Klawitter, "Rearrangement operations on unrooted phylogenetic networks", arXiv:1906.04468 (2019), Theorems 5.2, 5.5, 5.6, 5.9, 5.10, 5.11 and 5.12, Lemma 6.2, Theorems 6.4 and 6.5, <https://doi.org/10.48550/arXiv.1906.04468>.
