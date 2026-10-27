---
article_id: af_23c3df07208e707120ffd907
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ApproximateIdentity.approximate_identity_lemma
---

# Lemma 1 (Approximate Identity Lemma)

Let $f \in C(\mathbb{R}/2\pi\mathbb{Z})$, that is, $f$ is a continuous function on $\mathbb{R}$ such that $f(x+2\pi) = f(x)$. Let $K_N(x)$ satisfy: i) $\frac{1}{2\pi} \int_{-\pi}^{\pi} K_N(x) \, dx = 1$, ii) $\sup_{N} \int_{-\pi}^{\pi} |K_N(x)| \, dx \leq M$, iii) For any $\delta > 0$, $\int_{\delta \leq |x| \leq \pi} |K_N(x)| \, dx \to 0$ as $N \to \infty$. Then $\max_{x} |f(x) - f * K_N(x)| \to 0$ as $N \to \infty$.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.103 Fourier Analysis (Fall 2013), Fourier Series 2](../../../../sources/v1/FourierAnalysis.md)
