# Three-state reconstruction on a regular tree above Kesten–Stigum

For $-1/2\le\lambda\le1$, the three-state channel has transition probability $(1+2\lambda)/3$ to retain a color and $(1-\lambda)/3$ to take either specified different color. The root color is uniform. The observation $O_0$ is the root color; conditional on a color $i$, $O_{\ell+1}$ is the multiset of the $\ell$-level observations from the children, obtained by independently transmitting $i$ across each edge and recursing. This retains the unordered truncated tree shape and the depth-$\ell$ spins, not the spins of internal vertices. Let

$$
a_\ell=\sum_o P(O_\ell=o)\;\frac12\sum_{i=0}^2|P(\sigma_\varnothing=i\mid O_\ell=o)-1/3|,
$$

where zero-mass observations contribute zero. When every vertex has $b$ children, $b$ any natural number, $b\lambda^2>1$ implies that $a_\ell$ converges to a strictly positive real limit. Equivalently the branching premise may include $b\ge2$, which follows from $b\lambda^2>1$ and the range of $\lambda$.

**Conventions.** Use the recursive three-state broadcast law on multisets of observations and the expected posterior total variation from the uniform root law. This is not the population martingale limit about Galton–Watson generation size alone.

## Depends on

- [Three-state broadcast law and multiset observations](three-state-multiset-observation.md)

## Proof outline

A subtree-symmetric eigenfunction estimator with controlled second moment when $b\lambda^2>1$, a conversion of its nonzero root correlation into a uniform lower bound on expected posterior total variation, and data processing between successive observation laws.

Define the observation laws by finite independent child draws and forgetting sibling order, then show the estimator is measurable in that observation. Keep negative $\lambda$ in the estimator by its signed normalization; no assertion is made at or below the squared threshold.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ThreeStateTreeClauses.lean#L92-L95)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/229.md)
- [Accompanying manuscript: The exact reconstruction threshold for the three-state symmetric channel](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/The-exact-reconstruction-threshold-for-the-three-state-symmetric-channel-September-25-2026/paper.pdf)
- [Background: Kesten and Stigum, *Additional limit theorems for indecomposable multidimensional Galton–Watson processes*, Annals of Mathematical Statistics 37 (1966), 1463–1481](https://doi.org/10.1214/aoms/1177699139)
