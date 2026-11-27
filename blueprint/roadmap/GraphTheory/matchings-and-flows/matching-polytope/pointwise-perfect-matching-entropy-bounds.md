# Pointwise upper and lower bounds for matching entropy

For $m>0$, let a finite loopless multigraph on $2m$ vertices have a perfect matching, and take $x$ from the convex hull of the perfect-matching indicator vectors. For any edge vector $z$, write $F(z)=\sum_e -z_e\log z_e$ on $[0,1]^E$, with zero contributions when $z_e=0$. Let $H(x)$ be the supremum of Shannon entropy over all probability laws on perfect matchings with edge marginals $x$. Then

$$
F(x)-(2-2/m)F(1-x)\le H(x)\le F(x).
$$

The claim is pointwise, including boundary points of the polytope; parallel edges carry different coordinates.

## Depends on

- [Edges incident to a vertex in an endpoint-map multigraph](../../graph-families-and-operations/finite-multigraphs/incident.md), with distinct endpoints for each edge. A perfect matching uses exactly one incident edge at each vertex. The indicator vectors have one coordinate per edge label, including separate coordinates for parallel edges.

## Expansion

Separate shared law-fiber entropy attainment and boundary lower semicontinuity, then the exact sharp face/covariance input for the distinct refined objective (not the coarser exponential-deficit rank theorem). The support identity for product weights is also a separate reusable result: for feasible marginals, the nonnegative weights M ↦ ∏_{e∈M} x_e have total at most one and are positive on the support of each feasible law. Keep the strict-coefficient optimization, forced-edge induction and both final entropy comparisons in the leaf proof.

## Proof outline

Prove the lower bound by induction after forced-edge deletion for $\kappa>2-2/m$, then let $\kappa$ decrease to $2-2/m$. For the upper bound, compare any feasible law to the subprobability matching-product weights: the cross-entropy sum equals $F(x)$. For $m=1$ the correction vanishes and the law on parallel edges is the marginal itself.

## Sources

- [Comparator statement: `OAI.MatchingEntropyBounds.Refined.pointwise_entropy`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/MatchingEntropyBounds.lean#L73-L79)
- [Forced-edge argument and the strict-coefficient limit](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/MatchingEntropy/RefinedVariation.lean#L230-L328), and [the product-weight and entropy upper bounds](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/MatchingEntropy/RefinedVariation.lean#L445-L485)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/113.md)
- [Proof of the reduction and the prerequisite interfaces](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/MatchingEntropy/Main.lean)
