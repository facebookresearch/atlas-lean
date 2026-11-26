# Spherical code rate bounded by the closed hierarchy

For every real $0<s<1$, the asymptotic spherical code rate satisfies $R(s)\le L_{\rm cl}(s)$. The infimum uses $s\le2\Gamma$ at an interlacing tuple, not only $s<2\Gamma$.

## Depends on

- [Spherical code maximum and asymptotic rate](spherical-code-maximum-and-rate.md)
- [Interlaced variational objectives for spherical codes](interlaced-spherical-code-objectives.md)

## Proof depends on

- [Eventual spherical code bound from a feasible interlacing](eventual-code-bound-from-a-feasible-interlacing.md)
- [Strict refinement of a weakly feasible spherical-code tuple](strict-refinement-of-a-weakly-feasible-tuple.md)

## Proof outline

Strict tuples form a subset of the weakly feasible tuples. Conversely, strict refinement gives a strictly smaller value of $\Phi$ than any weakly feasible candidate, so the two infima agree once nonemptiness and lower boundedness are established. Apply the strict finite code estimate to bound the log-cardinality limsup, then use this equality of infima.

## Sources

- [OpenAI, *Ten Advances in Mathematics and Theoretical Computer Science*, Chapter 2](https://cdn.openai.com/pdf/ten-proofs-oai.pdf)
- [Pinned source: `main_general`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/B_SphericalCodes.lean#L266-L272)
