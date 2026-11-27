# Asymptotic binary code rate and the classical first bound

Let $A(n,d)$ be the largest cardinality of a subset of $\{0,1\}^n$ in which every pair of distinct words has Hamming distance at least the integer $d$ (distance counts differing coordinates). The relative-distance rate is

$$R(\delta)=\limsup_{n\to\infty}\frac{\log_2 A(n,\lceil\delta n\rceil)}{n}.$$

Here the ceiling is a natural number. For $0<\delta<1/2$, the classical comparison rate on this page is $R_1(\delta)=h(1/2-\sqrt{\delta(1-\delta)})$ with $h(u)=-u\log_2 u-(1-u)\log_2(1-u)$ and $0\log_2 0=0$. This convention does not require a distance constraint on equal words.

## Implementation notes

Use the Hamming metric and base-two normalization of binary entropy; establish that the finite maximum is nonzero, at most 2^n, and has the same relative-distance ceiling convention. Handle n=0 only as an irrelevant initial value for limsup.

## Sources

- [Pinned binary code, entropy and rate definitions](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/B_BinaryCodes.lean#L11-L53)
