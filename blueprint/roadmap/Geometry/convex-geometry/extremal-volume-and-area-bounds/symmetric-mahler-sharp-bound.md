# Sharp symmetric Mahler volume-product bound

Let $n\geq1$ and let $K\subseteq\mathbb R^n$ be compact, convex, symmetric about the origin and have nonempty interior. For $K^\circ=\{y:\sum_{i=1}^n y_ix_i\leq1\text{ for every }x\in K\}$ one has $|K|\,|K^\circ|\geq4^n/n!$. The volumes are coordinate Lebesgue volumes; the bound is asserted in every positive dimension.

## Depends on
- [Polar set](../../../Analysis/convex-analysis-and-variations/polar-sets/polar-set.md).

The coordinate dot product and measure must agree with their Euclidean model; symmetry and interior nonemptiness put the origin in the interior.

## Proof depends on
A sharp factorial-normalized lower bound, not merely an absolute positive base smaller than $4$.

## Expansion
Expose the dimension-dependent lower-bound argument and check its base case and volume transformations. Separate the lower bound from classification of the equality cases.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/MahlerConjecture.lean#L15-L21) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/087.md).
