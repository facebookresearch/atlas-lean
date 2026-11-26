# Partitional infinite matroids without an intersection witness

Write $D=\coprod_{m\ge0}\{f:\{0,1\}^m\to\{0,1\}\}$ and $E=\mathbb Z\times D$, which is countably infinite. There is a self-dual matroid $Q$ on all of $D\times\{0,1\}$ which is uniform in the sense that each subset of its ground set is independent or spanning. For parity $p=0,1$, construct $M_p$ on $E$ as the direct sum of copies of $Q$ indexed by the integers $z$ of parity $p$. In a copy, send $(x,b)$ to $(j,x)$, with $j=z$ when $z<0,b=0$ or $z\ge0,b=1$, and $j=z-1$ otherwise. These identifications are bijective for each parity. Both $M_p$ are self-dual with full ground set and partitional (direct sums of uniform components). They admit no full independent covering or packing/covering partition as defined in the [packing-covering predicate](infinite-matroid-packing-covering.md). They also admit no common independent set $J$ with a disjoint partition $J=J_0\sqcup J_1$ such that $\operatorname{cl}_{M_0}(J_0)\cup\operatorname{cl}_{M_1}(J_1)=E$.

## Depends on

- [Packing-covering partition predicate](infinite-matroid-packing-covering.md)
- Ray component equivalences, direct sum, duality, closure, and the precise intersection witness.

## Expansion

Separate the concrete full-ground-set uniform self-dual component on the prescribed carrier and its basis criterion before gluing the two parity ray matroids. Use two reusable implications with the exact retained-set contraction convention. First, for a pair of full-ground-set self-dual matroids, a packing/covering partition gives one independent set in each matroid whose union covers the ground set. Second, for matroids $M,N$ on a common ground set, an intersection witness for $M,N$ gives a packing/covering partition for $M,N^*$. In the ray construction the second matroid is self-dual, so the second implication and the previously ruled-out packing/covering partition exclude the intersection witness.

## Proof outline

Verify the component bijections at the sign boundary and connect the sum to the native matroid API. Prove all three failures for the same pair; arbitrary matroids with the first two failures need not preserve the extra ray form or intersection property.

## Sources

- [Comparator statement: `OAI.InfiniteMatroidCounterexample.partitional_intersection_counterexample`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/InfiniteMatroidCorollaries.lean#L108-L118)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/185.md)
- [Packing/covering gives an independent cover for a self-dual pair](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/InfiniteMatroid/PackingCovering.lean#L35-L38), [intersection implies packing/covering after dualizing the second matroid](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/InfiniteMatroid/IntersectionReduction.lean#L8-L9), and [the partitional construction](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/InfiniteMatroid/Corollaries.lean#L11-L48).
