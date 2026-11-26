# The space of nested ultrametric trees is CAT(0)

**Setting.** A nested (reconciled) tree of type $(n,m,\ell)$ consists of an ultrametric host tree on $n$ leaves, an ultrametric parasite tree on $m$ leaves, and a fixed leaf map $\ell:[m]\to[n]$, with the parasite tree embedded in the host tree. Ordering all internal (speciation) times of both trees, the *nesting sequence* records for each event whether it is a host ($H$) or parasite ($P$) speciation. A *nested ranked tree topology* is a host ranked topology, a parasite ranked topology, the leaf map and a compatible nesting sequence. Following the $\tau$-space construction for single ranked trees, each nested ranked topology contributes an orthant $\mathbb{R}_{\ge0}^{n+m-2}$ whose coordinates are the inter-event times; gluing orthants along faces that represent the same trees (coalescing event times, rank swaps, cospeciations) gives a cube complex $\Sigma_{n,m,\ell}$ ($\sigma$-space) with the induced piecewise Euclidean length metric.

**Theorem.** $\Sigma_{n,m,\ell}$ satisfies Gromov's cube condition: whenever three $(k+2)$-cubes share a common $k$-cube and pairwise share $(k+1)$-cubes, they lie in a common $(k+3)$-cube. Consequently $\sigma$-space is CAT(0); it is a connected length space with unique geodesics between any two nested trees.

## Expansion

By Gromov's link condition, a cube complex is locally CAT(0) when the link of every vertex is a flag simplicial complex, and the cube condition is the combinatorial form of this requirement; simple connectivity (each orthant contains the origin) then upgrades local to global CAT(0). The proof checks the condition on admissible nesting sequences, for instance that the link of the origin has no 3-cycle of top-dimensional orthants pairwise sharing facets. Unique geodesics make Fréchet means and other summary statistics of samples of reconciled trees well defined.

## Sources

- G. Grindstaff, R. S. Hoekzema, "Nested tree space: a geometric framework for co-phylogeny", arXiv:2604.05056, Section 3 (nesting sequences), definition of $\Sigma_{n,m,\ell}$, Theorems 35–36 and Corollary 37. <https://doi.org/10.48550/arXiv.2604.05056>
