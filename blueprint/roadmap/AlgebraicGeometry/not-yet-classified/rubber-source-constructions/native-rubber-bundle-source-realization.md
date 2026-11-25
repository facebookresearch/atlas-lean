# Native Rubber Bundle Source Realization

A strict cochain realization of the module diagram of a vector bundle stack: let $k$ be a field,
with the rubber target data `O`, `P`, `D`, `R`, `S` over $k$, a genus $g$, a ramification profile
$a \in \mathbb{Z}^n$, a rubber moduli model `B` and a vector bundle stack $E$ over its stack. Then
there is a `BundleRealization` of $E$: a global cochain complex of module presheaves on the affine
points of the stack, with a quasi-isomorphism from its value at every affine point $p$ to the cone
of the differential $E^0_p \to E^1_p$ of the module diagram of $E$ (both placed in degree $2$) and,
for every arrow $f : p \to q$, the map of cones induced by the restriction maps of the diagram
along $f$ and a homotopy between the two resulting maps from the value at $q$ to the restriction
along $f$ of the cone at $p$. These homotopies need not be compatible with identities and
composition.
