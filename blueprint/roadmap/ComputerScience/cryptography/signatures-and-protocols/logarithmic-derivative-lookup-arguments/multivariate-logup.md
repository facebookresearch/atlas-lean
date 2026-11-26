# Multivariate LogUp lookup argument via sum-check

Let $f,t:\{0,1\}^{s}\to\mathbb{F}$ be given by committed multilinear polynomials (padding to equal size). After committing to the multiplicity function $m$ and receiving $\alpha$, the claim $\sum_{x\in\{0,1\}^{s}}\bigl(\frac{m(x)}{\alpha-t(x)}-\frac{1}{\alpha-f(x)}\bigr)=0$ is proved by committing to helper functions $h_f=1/(\alpha-f)$ and $h_t=m/(\alpha-t)$, running one sum-check for $\sum_x(h_t(x)-h_f(x))=0$ and a batched zero-check for $h_f(\alpha-f)-1=0$ and $h_t(\alpha-t)-m=0$. The result is a lookup argument whose prover cost is linear in $2^{s}$ field operations plus commitments to $m,h_f,h_t$, with soundness error $O((2^{s+1}+s)/|\mathbb{F}|)$; vector lookups of width $k$ are reduced to scalar ones by a random linear combination $\sum_\ell\theta^{\ell}f^{(\ell)}$ with additional error $(k-1)/|\mathbb{F}|$ per pair of distinct tuples.

## Proof sketch

Correctness of the helper columns is a zero-check; the sum equals the logarithmic-derivative difference at $\alpha$, so the random-evaluation lemma bounds soundness. Distinct tuples collide under a random linear combination with probability at most $(k-1)/|\mathbb{F}|$.

## Depends on

- [Soundness of checking the logarithmic-derivative identity at a random point](logup-random-evaluation.md)
- [Zero-check reduction to sum-check via the equality polynomial](../plonkish-polynomial-iops/zerocheck-reduction.md)
- [The sum-check protocol](../../../../TheoryOfComputation/randomized-and-quantum-complexity/interactive-proofs/the-sum-check-protocol.md)

## Proof depends on

- [Soundness of checking the logarithmic-derivative identity at a random point](logup-random-evaluation.md)
- [Zero-check reduction to sum-check via the equality polynomial](../plonkish-polynomial-iops/zerocheck-reduction.md)
- [The sum-check protocol](../../../../TheoryOfComputation/randomized-and-quantum-complexity/interactive-proofs/the-sum-check-protocol.md)

## Sources

- Ulrich Haböck, "Multivariate Lookups Based on Logarithmic Derivatives", IACR ePrint 2022/1530 (2022).
