# Limit slopes for the least missing denominator

Let $v(k)$ be the infimum of the natural numbers $m\ge2$ which do not occur among the
denominators of any exact $k$-term strictly increasing positive denominator expansion of one.
Put $S(k)=\log\log v(k)/k$ as a real quotient (division by
zero is totalized for $k=0$). With limits taken through the naturals,

$$
\frac{\log2}{257}\le\liminf_{k\to\infty}S(k)\le\limsup_{k\to\infty}S(k)\le\log2.
$$

## Proof depends on

- [Exact-marker padding](pad-an-expansion-preserving-denominator.md)
- [Occurrence of every marker](../exists-expansion-one-with-denominator.md)
- [Quantitative marker length](quantitative-prescribed-denominator.md)
- [Least missing denominator characterization and upper bound](least-missing-denominator.md)

## Expansion

Use the quantitative construction and the padding lemma to cover all small markers at the exact target length, including the finite initial range separately. Track the exponential inversion for the lower slope, and use the pointwise bound on $v(k)$ for the upper slope.

## Sources

- [EgyptianFractions.lean — `prescribed_denominator_corollary`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EgyptianFractions.lean#L107-L119)
- [Source missing set, infimum and slope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EgyptianFractions.lean#L35-L46)
