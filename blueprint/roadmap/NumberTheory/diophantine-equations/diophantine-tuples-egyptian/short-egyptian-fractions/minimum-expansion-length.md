# The minimum Egyptian length is attained

For natural numbers $1\le a<b$, let $L(a,b)$ be the infimum of lengths $k\in\mathbb N$ of
Egyptian denominator tuples $(n_0,\ldots,n_{k-1})\in\mathcal E_k^{<}$ whose reciprocals sum to $a/b$
in $\mathbb Q$. The tuple condition is the existing one: strictly increasing, with each denominator
at least two. Then such a tuple exists at length $L(a,b)$ and every such tuple of length $k$
satisfies $L(a,b)\le k$. The input fraction need not be reduced.

## Depends on

- [Strictly increasing Egyptian denominator tuples](../egyptian-fraction-underapproximations/is-strict-egyptian.md)

## Proof depends on

- [Existence of an Egyptian expansion of a proper rational](../exists-expansion-of-proper-rational.md)

## Proof outline

Use greedy existence to prove the length set nonempty, then apply the minimum principle for natural numbers. Relate strictly increasing lists to strictly increasing tuples with the same length and rational reciprocal sum.

## Sources

- [EgyptianFractions.lean — `egyptian_length_is_minimum`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EgyptianFractions.lean#L48-L56)
- [Source exact-expansion and infimum definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EgyptianFractions.lean#L11-L23)
