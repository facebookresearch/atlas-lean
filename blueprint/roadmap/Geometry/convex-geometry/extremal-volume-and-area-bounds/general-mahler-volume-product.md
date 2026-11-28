# General Mahler volume-product bound and simplex equality

Let $n\geq1$ and let $K\subset\mathbb R^n$ be compact and convex with nonempty interior. For $z\in\operatorname{int}K$ put $K_z^\circ=\{y:y\cdot(x-z)\leq1\text{ for every }x\in K\}$ and $M(K)=\inf_z |K|\,|K_z^\circ|$, with Euclidean Lebesgue volume. Then $M(K)\geq(n+1)^{n+1}/(n!)^2$, with equality if and only if $K$ is the convex hull of $n+1$ affinely independent points. The center ranges over the interior, without a symmetry assumption.

## Depends on
- [Polar set](../../../Analysis/convex-analysis-and-variations/polar-sets/polar-set.md), applied to the translated body.

## Proof depends on
Control of the translated polar volume as the center varies, the sharp lower estimate for nonsymmetric bodies, and the rigidity implication at equality.

## Expansion
Separate the interior center minimization, explicit simplex evaluation, sharp inequality and equality rigidity. Keep the Euclidean volume normalization instead of importing the symmetric result or a functional analogue.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/GeneralMahler.lean#L23-L33) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/087.md).
