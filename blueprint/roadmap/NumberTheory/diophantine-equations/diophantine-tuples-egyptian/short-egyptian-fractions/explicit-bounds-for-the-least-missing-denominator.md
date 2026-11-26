# Explicit eventual bounds for the least missing denominator

Let $v(k)$ be the infimum of the natural numbers $m\ge2$ which do not occur among the
denominators of any exact $k$-term strictly increasing positive denominator expansion of one.
There is a natural $k_0$ such that every
natural $k\ge k_0$ satisfies

$$
\exp(\exp(k/600))\le v(k)\le1+k^{2^{k-1}}.
$$

## Proof depends on

- [Subcritical double-exponential bound](subcritical-lower-bound-for-the-least-missing-denominator.md)
- [Least missing denominator upper bound](least-missing-denominator.md)

## Proof outline

For the lower bound compare $1/600$ with $\log2/257$ and apply the subcritical estimate. For the upper bound use the first-missing characterization and the upper bound on all admissible denominators at length $k$.

## Sources

- [EgyptianFractions.lean — `prescribed_denominator_corollary`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EgyptianFractions.lean#L107-L119)
- [Source missing set, infimum and slope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EgyptianFractions.lean#L35-L46)
