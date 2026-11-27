# Subcritical double-exponential bounds for the least missing denominator

Let $v(k)$ be the infimum of the natural numbers $m\ge2$ which do not occur among the
denominators of any exact $k$-term strictly increasing positive denominator expansion of one.
For every real $c<\log2/257$, for all
sufficiently large natural $k$,

$$
v(k)\ge\exp(\exp(ck)).
$$

The endpoint $c=\log2/257$ is not asserted in this eventual lower bound.

## Proof depends on

- [Lower limit slope](limit-slopes-of-the-least-missing-denominator.md)
- [Lower bound on the least missing denominator](least-missing-denominator.md)

## Proof outline

Turn the strict subcritical exponent into an eventual lower bound on the double-logarithmic quotient, then invert both logarithms. Check that $v(k)\ge2$ and that the tail indices used are positive.

## Sources

- [EgyptianFractions.lean — `prescribed_denominator_corollary`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EgyptianFractions.lean#L107-L119)
- [Source missing set, infimum and slope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EgyptianFractions.lean#L35-L46)
