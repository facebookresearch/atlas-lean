# A simplex does not maximize projection volume in dimension twenty

For a convex body $K\subset\mathbb R^n$ (compact, convex, with nonempty interior), write $b_K(u)$ for the induced $(n-1)$-dimensional Euclidean volume of the orthogonal shadow on $u^\perp$ for $\|u\|=1$. Put $\Pi K=\{x:\langle u,x\rangle\le b_K(u)\text{ for all unit }u\}$ and $R(K)=|\Pi K|/|K|^{n-1}$.

Here the shadow area is equivalently intended as Euclidean-normalized Hausdorff measure in the ambient space, of dimension $19$. For $\Delta_{20}=\operatorname{conv}(0,e_1,\dots,e_{20})$, it is false that all convex bodies $P\subset\mathbb R^{20}$ satisfy $R(P)\le R(\Delta_{20})$. This is a single dimension, not an asymptotic growth statement.

## Depends on

- [Convex body](../../../packings-and-coverings/hadwiger-covering-and-illumination-problem/is-convex-body.md)
- Euclidean Hausdorff shadow measure and its comparison with induced hyperplane volume.

## Proof depends on

- [Product of two ten-simplices](product-of-two-simplices.md)
- Evaluate $R(\Delta_{20})=21\cdot20^{20}/20!$ with the same normalization.

## Expansion

Verify the measure comparison on the actual projection image, then insert the product witness and negate the universal upper bound. The exact product ratio is a separate result.

## Sources

- OpenAI Math, [`universal_simplex_upper_bound_false`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ProjectionCounterexample.lean#L37-L40) (statement and local definitions).
