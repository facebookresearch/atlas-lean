# The additive indecomposability of the primes

For any $A,B\subseteq\mathbb N$, each containing at least two distinct elements, the symmetric
difference between $A+B=\{a+b:a\in A,\ b\in B\}$ and the set of primes is infinite. Equivalently,
no finite modification of the primes is such a sumset. Either summand is allowed to be finite;
both can contain zero.

## Proof depends on

- [Two infinite summands](two-infinite-summands.md)

## Expansion

Separate the two-infinite-summands case from the remaining cases; rule out a nontrivial finite summand using the prime constraints on translations. Show the equivalence of finite symmetric difference and eventual membership agreement over the natural numbers.

## Sources

- [OstmannPrimes.lean — `main`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/OstmannPrimes.lean#L9-L12)
- [OstmannComplete.lean — `inverseGoldbach`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/OstmannComplete.lean#L30-L32)
