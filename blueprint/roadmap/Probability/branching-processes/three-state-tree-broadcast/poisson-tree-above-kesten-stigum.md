# Three-state reconstruction on a Poisson tree above Kesten–Stigum

Use the [three-state channel and recursive observations](three-state-multiset-observation.md), but at each vertex take an independent Poisson number of children of mean $d\ge0$, independent of the color transmissions. Thus, conditional on the starting color, first draw the child count with mass $e^{-d}d^j/j!$, then form the multiset of independent noisy child observations. Average the posterior total-variation advantage over the joint tree and spin law, including extinct trees. If $d\lambda^2>1$, that advantage converges with depth to a strictly positive real limit. The stronger-looking requirement $d>1$ is already forced by this premise and $-1/2\le\lambda\le1$.

Use independent branching with Poisson offspring; this is not reconstruction conditioned on nonextinction or on an individual realized tree.

## Depends on

- [Three-state broadcast law and multiset observations](three-state-multiset-observation.md)

## Proof outline

Second-moment control of the signed eigenfunction sum with a random number of offspring, expectation over the generation tree, and data processing to ensure a limit.

Bridge the Poisson product and recursive generation laws; prove the variance recursion using the second factorial moment of Poisson offspring. Convert the resulting correlation bound for the unconditional tree-and-spin law to a positive limiting posterior total-variation advantage, without excluding extinction.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ThreeStateTreeClauses.lean#L96-L99)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/229.md)
- [Accompanying manuscript: The exact reconstruction threshold for the three-state symmetric channel](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/The-exact-reconstruction-threshold-for-the-three-state-symmetric-channel-September-25-2026/paper.pdf)
- [Background: Kesten and Stigum, *Additional limit theorems for indecomposable multidimensional Galton–Watson processes*, Annals of Mathematical Statistics 37 (1966), 1463–1481](https://doi.org/10.1214/aoms/1177699139)
