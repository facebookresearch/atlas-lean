# Regular-tree supercritical advantage with the uniform null posterior

Let $b\ge2$ be a natural number and $b\lambda^2>1$. Assume $-1/2\le\lambda\le1$. Take the uniform three-state root and exactly $b$ children at each vertex. The initial observation is its root color. At each subsequent depth, draw each child color independently through the channel with diagonal probability $(1+2\lambda)/3$ and off-diagonal probability $(1-\lambda)/3$, recurse, and forget the order of the observed child list. On a zero-mass observation the posterior is the uniform prior; on a positive-mass observation it is the conditional root law. The advantage is the real sum of marginal mass times total variation from the uniform prior, over all possible observations at that depth. Then this sequence converges to a strictly positive real limit.

## Depends on

- [Three-state broadcast law and multiset observations](three-state-multiset-observation.md)

## Proof depends on

Identify the observed-law recursion, marginal and advantage in the two comparator representations; use the supercritical reconstruction estimate only after that identification.

## Expansion

This formulation retains the source's explicit branching assumption and uniform posterior fallback. Compare the channel atoms and offspring laws, transport the recursively defined observations, and prove equality of weighted advantages before identifying it with the closely related [other formulation](regular-tree-above-kesten-stigum.md).

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ThreeStateSupercritical.lean#L98-L101)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/229.md)
- [Accompanying manuscript: The exact reconstruction threshold for the three-state symmetric channel](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/The-exact-reconstruction-threshold-for-the-three-state-symmetric-channel-September-25-2026/paper.pdf)
