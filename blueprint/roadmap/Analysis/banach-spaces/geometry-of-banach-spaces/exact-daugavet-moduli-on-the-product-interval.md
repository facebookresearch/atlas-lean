# A product-interval space with exact asymptotic moduli and no AUC renorming

There exists a subspace $E$ of real $L^1$ on the countable product of uniform $[0,1]$ such that all the closedness, infinite dimension, whole-unit-ball measure-cover, unit-slice and rank-one Daugavet conclusions in [the product-interval construction](kadets-werner-measure-precompact-daugavet-space.md) hold. On this same $E$, at every unit $x$ and every $t>0$, the averaged and one-sided cofinite moduli $H(x,t),D(x,t)$ of [the exact modulus formulas](exact-asymptotic-moduli-for-measure-precompact-daugavet-spaces.md) equal $\max(t/2,t-1)$ and $\max(0,t-2)$. The infima over unit $x$ retain these equalities for all $t>0$, and no equivalent norm is AUC.

## Depends on

- [Definitions of the two cofinite moduli](exact-asymptotic-moduli-for-measure-precompact-daugavet-spaces.md).

## Proof depends on

- [The product-interval construction](kadets-werner-measure-precompact-daugavet-space.md) and [the general formulas](exact-asymptotic-moduli-for-measure-precompact-daugavet-spaces.md).

## Expansion

Combine the construction and the general formulas without changing the inherited $L^1$ norm or choosing a different subspace for each radius. Retain the unit-slice assertion on the output witness.

## Sources

- OpenAI, [DaugavetModuli comparator, exact_example](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/DaugavetModuli.lean#L91-L103).
- OpenAI, [scope and accompanying papers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/331.md).
