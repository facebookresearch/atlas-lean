# Algebraicity of rational Hodge classes on CM abelian varieties

Let $X$ be a smooth integral projective group scheme over $\mathbb C$. Assume that the geometric rational $H^1(X;\mathbb Q)$ is isomorphic over $\mathbb Q$ to a finite direct sum of rank-one spaces over CM number fields, with possibly different fields in different summands. For every element of the product of these fields, its transported diagonal action on the complexified $H^1$ preserves the inverse image of the holomorphic filtration $F^1$ under the comparison with de Rham cohomology.

For every $p\ge0$, the rational classes in degree $2p$ whose de Rham images lie in $F^p\cap\overline{F^p}$ are contained in the rational span of the cohomology classes of codimension-$p$ algebraic subvarieties of $X$. Here $\overline{F^p}$ consists of the classes whose conjugates lie in $F^p$, with conjugation induced by conjugating constant complex coefficients. This is a statement about the prescribed geometric cohomology and cycle-class map; it does not state a Tate or standard-conjecture consequence.

## Depends on

- Geometric Betti and de Rham cohomology with comparison and filtration, rational algebraic cycle classes, and the diagonal CM action.

## Proof depends on

- Reduction to the CM character decomposition and the algebraic realizations of its rational Hodge classes, with comparison to the geometric cycle span.

## Expansion

Bridge the existing abstract Hodge structures to these geometric cohomology groups, check the precise CM rank-one action and its filtration condition, then isolate the algebraicity step rather than assuming a generic cycle surjectivity interface.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/HodgeConjectureCMAbelianVarieties/Challenge.lean#L36-L44), [complex multiplication on geometric H¹](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/HodgeConjectureCMAbelianVarieties/CM.lean#L35-L58), and [the rational Hodge-class subspace](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/HodgeConjectureCMAbelianVarieties/HodgeConjecture/Definitions/AlgebraicGeometry/Hodge/Filtration.lean#L930-L956).
