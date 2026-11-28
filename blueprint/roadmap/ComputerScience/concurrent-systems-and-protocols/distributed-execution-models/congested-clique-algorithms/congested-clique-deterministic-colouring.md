# Deterministic constant-round (Delta+1)-colouring in the congested clique

In the congested clique, a proper $(\Delta + 1)$-colouring of an $n$-vertex input graph of maximum degree $\Delta$ can be computed deterministically in $O(1)$ rounds. More generally, $(\Delta + 1)$-list colouring, in which every vertex must receive a colour from its own list of $\Delta + 1$ colours (lists of size at least $\deg(v) + 1$, as in $(\deg + 1)$-list colouring), can be solved deterministically in $O(1)$ rounds.

## Proof sketch

The algorithm is a recursive procedure ColorReduce$(G, \ell)$, called first with $\ell = \Delta$. If $G$ has $O(n)$ edges and vertices, it is gathered at one processor by Lenzen routing and coloured locally; this is the base case. Otherwise the vertices are hashed into about $\ell^{0.1}$ bins and the colours into all but the last bin, each vertex's list being restricted to the colours of its own bin. Vertices whose degree within their bin or whose restricted list size deviates too far from the expected value $\ell^{-0.1}$ times the original are declared bad. The good vertices of every bin except the last then have more available colours than neighbours in their bin, with palettes disjoint across bins, so these bins recurse in parallel with degree bound about $\ell^{0.9}$. Afterwards the last bin, whose lists are updated by removing colours of already coloured neighbours, recurses with the same bound, and finally the graph of bad vertices, of size $O(n)$, is gathered and coloured locally. The hash functions are chosen deterministically from limited-independence families by the method of conditional expectations so that no bin is overfull and there are few bad vertices. After a constant number of recursion levels every instance has size $O(n)$, giving $O(1)$ rounds.

## Depends on

- [The congested clique model](the-congested-clique-model.md)
- [The (deg + 1)-list-coloring problem (D1LC)](../../../randomized-algorithms/sketching-streaming-and-sublinear-algorithms/palette-sparsification-and-sublinear-coloring/degree-plus-one-list-coloring.md)

## Proof depends on

- [Lenzen's deterministic constant-round routing and sorting in the congested clique](congested-clique-constant-round-routing.md)

## Sources

- A. Czumaj, P. Davies, M. Parter, "Simple, Deterministic, Constant-Round Coloring in the Congested Clique", PODC 2020, arXiv:2009.06043, Theorem 1, Algorithms 1 and 2, and Section 3.
