# Deterministic constant-round (Delta+1)-colouring in the congested clique

In the congested clique, a proper $(\Delta + 1)$-colouring of an $n$-vertex input graph of maximum degree $\Delta$ can be computed deterministically in $O(1)$ rounds.

## Proof sketch

Randomly partition (then derandomize via limited-independence hash families and the method of conditional expectations) the vertices into $\sqrt\Delta$ groups and the palette into matching sub-palettes, so that each group induces a subgraph with $O(n)$ edges and degree compatible with its sub-palette. Each group's subgraph is routed to one processor by Lenzen routing and coloured locally; a constant number of rounds handles the few vertices whose degree constraints fail, again by collecting them at single processors.

## Depends on

- [The congested clique model](the-congested-clique-model.md)
- [The (deg + 1)-list-coloring problem (D1LC)](../../../randomized-algorithms/palette-sparsification-and-sublinear-coloring/degree-plus-one-list-coloring.md)

## Proof depends on

- [Lenzen's deterministic constant-round routing and sorting in the congested clique](congested-clique-constant-round-routing.md)

## Sources

- A. Czumaj, P. Davies, M. Parter, "Simple, Deterministic, Constant-Round Coloring in the Congested Clique", PODC 2020, arXiv:2009.06043.
