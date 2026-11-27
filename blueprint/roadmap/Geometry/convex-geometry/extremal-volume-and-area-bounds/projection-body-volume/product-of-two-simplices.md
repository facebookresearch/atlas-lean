# Projection volume of the product of two ten-simplices

For a convex body $K\subset\mathbb R^n$ (compact, convex, with nonempty interior), write $b_K(u)$ for the induced $(n-1)$-dimensional Euclidean volume of the orthogonal shadow on $u^\perp$ for $\|u\|=1$. Put $\Pi K=\{x:\langle u,x\rangle\le b_K(u)\text{ for all unit }u\}$ and $R(K)=|\Pi K|/|K|^{n-1}$.

Let $\Delta_d=\operatorname{conv}(0,e_1,\dots,e_d)$ and $P=\Delta_{10}\times\Delta_{10}$ in the two coordinate blocks of $\mathbb R^{20}$. Write $S_d=(d+1)d^d/d!$. Then $P$ is a convex body and

$$\frac{R(P)}{S_{20}}=\frac{121\binom{20}{10}}{21\,2^{20}}=\frac{22355476}{22020096}>1,\qquad |\Pi P|>S_{20}|P|^{19}.$$

The source also defines brightness on nonunit $u$ by multiplying the induced shadow volume by $\|u\|$ (and hence taking value zero at $u=0$).

## Depends on

- [Convex body](../../../packings-and-coverings/hadwiger-covering-and-illumination-problem/is-convex-body.md)
- Coordinate simplex and Euclidean product; projection-body brightness with homogeneous extension.

## Proof depends on

- Exact brightness and volume formulas for the chosen product, then the explicit rational comparison.

## Expansion

Prove product-body compactness/interior and the projection-body volume formula before evaluating the two exact fractions. Keep this formula distinct from the universal-upper-bound negation until the simplex normalization is proved.

## Sources

- OpenAI Math, [`product_counterexample`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ProjectionVolume.lean#L45-L56) (statement and local definitions).
