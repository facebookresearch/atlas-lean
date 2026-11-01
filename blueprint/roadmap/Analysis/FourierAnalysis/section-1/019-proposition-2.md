---
article_id: af_a3cc4cd888f6f66138b890cf
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: FourierTransformMeasure.schwartz_weak_convergence_of_fourierTransform_tendsto
---

# Proposition 2 (Section 1, Fourier Integrals of finite measures)

If $\mu_j$ and $\mu$ belong to $M_+(\mathbb{R})$, and for each $\xi \in \mathbb{R}$, $\lim_{j \to \infty} \hat{\mu}_j(\xi) = \hat{\mu}(\xi)$, then $\lim_{j \to \infty} \int_{\mathbb{R}} f \, d\mu_j = \int_{\mathbb{R}} f \, d\mu$ for all $f \in \mathcal{S}(\mathbb{R})$.

## Depends on

- [Proposition 1 (Section 1, Fourier Integrals of finite measures)](017-proposition-1.md)

## Proof depends on

- [Theorem 1 (Section 1: Fourier Integrals on $L^2(\mathbb{R})$ and $L^1(\mathbb{R})$)](007-theorem-1.md)

## Sources

- [MIT 18.103 Fourier Analysis (Fall 2013), Section 1, Fourier Integrals of finite measures](../../../../sources/v1/FourierAnalysis.md)
