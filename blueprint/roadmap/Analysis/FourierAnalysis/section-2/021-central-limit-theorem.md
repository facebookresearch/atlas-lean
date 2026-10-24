---
article_id: af_56da4600a142062a8ee1c2f8
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: CentralLimitTheorem.central_limit_theorem
---

# Theorem 2 (Central Limit Theorem)

Let $X_1, X_2, \ldots$ be independent, identically distributed random variables such that $\mathbb{E}(X_1) = M$, $\mathbb{E}[(X_1 - M)^2] = \sigma^2$, and $\mathbb{E}(|X_1|^{2+\alpha}) = A < \infty$ for some $\alpha > 0$. Then $$\mathbb{P}\!\left(a < \frac{X_1 + \cdots + X_n - nM}{\sqrt{n}} < b\right) \longrightarrow \int_a^b g_\sigma(x) \, dx.$$

## Depends on

This node has no prerequisites.

## Proof depends on

- [Proposition 1 (Section 1, Fourier Integrals of finite measures)](../section-1/017-proposition-1.md)
- [Proposition 2 (Section 1, Fourier Integrals of finite measures)](../section-1/019-proposition-2.md)
- [Proposition 3](../section-1/020-proposition-3.md)
- [Lemma 1 (Section 2, An application to the central limit theorem)](022-lemma-1.md)

## Sources

- [MIT 18.103 Fourier Analysis (Fall 2013), Section 2, An application to the central limit theorem](../../../../sources/v1/FourierAnalysis.md)
