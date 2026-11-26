# Spherical code maximum and asymptotic rate

For dimension $n$ and cutoff $s$, a spherical code is a finite set of unit vectors in $\mathbb R^n$ such that any two distinct vectors have inner product at most $s$. Let $M(n,s)$ be the supremum of the sizes of these sets in $\mathbb N\cup\{\infty\}$. The real rate $R(s)$ is the limsup as $n\to\infty$ of $n^{-1}\log_2 M(n,s)$, with $M$ converted to a natural number before taking the logarithm. For $0<s<1$, positive separation makes $M(n,s)$ finite and for $n>0$ it is positive. The kissing number uses $s=1/2$.

## Implementation notes

Use compactness of the unit sphere and positive separation to bound code size before converting out of the extended naturals. Prove the largest cardinality is attained and bridge the inner-product convention for kissing configurations.

## Sources

- [Pinned code and maximum definitions](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/B_SphericalCodes.lean#L151-L163)
- [Pinned rate definition](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/B_SphericalCodes.lean#L239-L244)
