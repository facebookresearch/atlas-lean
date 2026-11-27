# Power saving over the four-thirds planar unit-distance bound

For each natural number $n$, let $u(n)$ be the supremum of the numbers of unordered pairs at distance exactly one in $n$-point subsets of the Euclidean plane. Then there exist real numbers $C>0$ and $1\le\beta<4/3$ such that $u(n)\le Cn^\beta$ for every $n$, including $0$ and $1$. The same $C,\beta$ work for all $n$. The source counts via symmetric pairs; diagonal pairs do not contribute since their distance is zero.

## Depends on

- [Number of unit distances](unit-dist-num.md)
- Equivalence of the symmetric-pair count and the existing unordered count (half of the off-diagonal ordered count), and its size-indexed supremum.

## Proof depends on

- Establish a strict power saving, not merely a better constant in the classical bound.

## Expansion

Bridge the source’s symmetric-square filter to the existing count using the two orientations per pair. Then isolate the power-saving estimate that supplies an exponent strictly below $4/3$. This is neither the existing classical upper bound nor the negation of a subpower conjecture.

## Sources

- OpenAI Math, [`main`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/PlanarUnitDistances.lean#L19-L22) (statement and local definitions).
