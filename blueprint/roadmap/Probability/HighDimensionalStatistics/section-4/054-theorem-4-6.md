---
article_id: af_c076a601e7b9d4559ad00df0
declaration: theorem
origin: cited
lean: Rigollet.Chapter4.Thm_4_6.theorem_4_6
---

# Theorem 4.6

Let $X_1, \ldots, X_n$ be $n$ i.i.d. sub-Gaussian random vectors such that $\mathbb{E}[XX^{\top}] = \Sigma$ and $X \sim \mathsf{subG}_d(\|\Sigma\|_{\mathrm{op}})$. Then $$\|\hat{\Sigma} - \Sigma\|_{\mathrm{op}} \lesssim \|\Sigma\|_{\mathrm{op}} \left(\sqrt{\frac{d + \log(1/\delta)}{n}} \vee \frac{d + \log(1/\delta)}{n}\right)$$ with probability $1 - \delta$.

## Depends on

- [Definition 1.2](../chapter-1/002-definition-1-2.md)

## Proof depends on

- [Definition 1.17](../section-1/017-definition-1-17.md)
- [Lemma 1.18](../section-1/018-lemma-1-18.md)
- [Definition 1.11](../section-1/011-definition-1-11.md)
- [Lemma 1.12](../section-1/012-lemma-1-12.md)
- [Theorem 1.13 (Bernstein's inequality)](../section-1/013-bernstein-s-inequality.md)

## Sources

- [MIT 18.S997 High-Dimensional Statistics (Spring 2015), Section 4.3](../../../../sources/v1/HighDimensionalStatistics.md)
