# Eventual spherical code bound from a feasible interlacing

Fix $0<s<1$. For every level $r$, real exponent $B$, and interlacing arrays $(a,b)$ at level $r$ with $s<2\Gamma(a,b)$ and $\Phi(a,b)<B$, every spherical code $C$ with cutoff $s$ in every sufficiently large dimension $n$ satisfies $|C|<2^{Bn}$. The dimension cutoff may depend on the arrays and $B$, not on the code.

## Depends on

- [Spherical code maximum and asymptotic rate](spherical-code-maximum-and-rate.md)
- [Interlaced variational objectives for spherical codes](interlaced-spherical-code-objectives.md)

## Expansion

Build the interlaced spectral certificates and establish their asymptotics for the finite-dimensional code bound. Check that the eventual error is independent of the code in each dimension.

## Sources

- [OpenAI, *Ten Advances in Mathematics and Theoretical Computer Science*, Chapter 2](https://cdn.openai.com/pdf/ten-proofs-oai.pdf)
- [Pinned source: `main_general`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/B_SphericalCodes.lean#L266-L272)
