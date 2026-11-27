# Eventual kissing number upper bound with exponent 0.39661

In every sufficiently large integer dimension $n$, the kissing number $M(n,1/2)$ is at most $2^{0.39661n}$. The comparison is non-strict and the decimal is exact. The finite kissing number is converted to a real before comparison.

## Depends on

- [Spherical code maximum and asymptotic rate](spherical-code-maximum-and-rate.md)

## Proof depends on

- [Spherical code rate bounded by the localized hierarchy](localized-spherical-code-rate-upper-bound.md)

## Expansion

Certify a sufficiently strong exponent at s=1/2 with rigorous enclosures and verify that the asymptotic bound gives an eventual unscaled upper bound with the stated decimal.

## Sources

- [OpenAI, *Ten Advances in Mathematics and Theoretical Computer Science*, Chapter 2](https://cdn.openai.com/pdf/ten-proofs-oai.pdf)
- [Pinned source: `eventually_kissingNumber_lt_published`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/B_SphericalCodes.lean#L288-L291)
- [Strict numerical slack in the formal source](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/MetricCodes.lean#L25654-L25656)
- [Formal proof of the eventual kissing-number bound](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/MetricCodes.lean) (`eventually_kissingNumber_lt_published`).
