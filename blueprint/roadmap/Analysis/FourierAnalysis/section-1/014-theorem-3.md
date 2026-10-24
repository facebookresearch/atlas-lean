---
article_id: af_723fead791e20ff8afa485b0
declaration: theorem
origin: cited
statement: formalized
lean: CesaroSummation.cesaro_L1_convergence
---

# Theorem 3

Let $f \in L^1(\mathbb{R})$ and denote $\sigma_N(x) = \frac{1}{2\pi} \int_{-N}^{N} (1 - |\xi/N|)^+ \hat{f}(\xi) e^{ix\xi} \, d\xi$. Then $\lim_{N \to \infty} \|f - \sigma_N\|_{L^1} = 0$.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Theorem 4 (Approximate identity)](016-approximate-identity.md)
- [Proposition 2 (Section 1: Fourier Integrals on $L^2(\mathbb{R})$ and $L^1(\mathbb{R})$)](009-proposition-2.md)
- [Theorem 2 (Section 1: Fourier Integrals on $L^2(\mathbb{R})$ and $L^1(\mathbb{R})$)](010-theorem-2.md)
- [Corollary 4 (Fourier inversion on $L^2$)](013-fourier-inversion-on-l-2.md)

## Sources

- [MIT 18.103 Fourier Analysis (Fall 2013), Section 1: Fourier Integrals on $L^2(\mathbb{R})$ and $L^1(\mathbb{R})$](../../../../sources/v1/FourierAnalysis.md)
