# Petty’s projection-volume lower bound and equality

For a convex body $K\subset\mathbb R^n$ (compact, convex, with nonempty interior), write $b_K(u)$ for the induced $(n-1)$-dimensional Euclidean volume of the orthogonal shadow on $u^\perp$ for $\|u\|=1$. Put $\Pi K=\{x:\langle u,x\rangle\le b_K(u)\text{ for all unit }u\}$ and $R(K)=|\Pi K|/|K|^{n-1}$.

For every integer $n\ge4$ and every such $K$, $R(K)\ge\kappa_{n-1}^{n}\kappa_n^{2-n}$, where $\kappa_j$ is the $j$-dimensional volume of the closed Euclidean unit ball. Equality holds if and only if $K$ is a translate of the image of the closed unit ball under an invertible real-linear map. No smoothness, symmetry, or normalization is required.

## Depends on

- [Convex body](../../../packings-and-coverings/hadwiger-covering-and-illumination-problem/is-convex-body.md)
- Projection-body half-space construction and intrinsic Euclidean volume on hyperplanes.

## Proof depends on

- Affine invariance; sharp lower bound for all convex bodies; equality rigidity in both directions.

## Expansion

Set up brightness in the ambient and subspace measures and prove that the two agree with the chosen Hausdorff normalization. Expand the lower-bound argument and equality rigidity separately; this is not the polar projection inequality.

## Sources

- OpenAI Math, [`petty_projection_volume`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/PettyProjectionVolume.lean#L43-L50) (statement and local definitions).
