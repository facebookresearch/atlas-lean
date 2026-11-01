---
article_id: af_34f330912f3d1be2e7ae317b
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: TruncatedFourierInversion.truncated_fourier_inversion_L2
---

# Theorem 2 (Section 1: Fourier Integrals on $L^2(\mathbb{R})$ and $L^1(\mathbb{R})$)

Suppose that $f \in L^2(\mathbb{R})$. Then $\hat{f}(\xi) \mathbf{1}_{[-N,N]}(\xi)$ is in $L^2(\mathbb{R}) \cap L^1(\mathbb{R})$ and $s_N(x) = \frac{1}{2\pi} \int_{-N}^{N} \hat{f}(\xi) e^{ix\xi} \, d\xi$ satisfies $\lim_{N \to \infty} \|f - s_N\|_{L^2} = 0$.

## Depends on

- [Corollary 2 (Section 1: Fourier Integrals on $L^2(\mathbb{R})$ and $L^1(\mathbb{R})$)](011-corollary-2.md)

## Proof depends on

- [Proposition 2 (Section 1: Fourier Integrals on $L^2(\mathbb{R})$ and $L^1(\mathbb{R})$)](009-proposition-2.md)
- [Corollary 4 (Fourier inversion on $L^2$)](013-fourier-inversion-on-l-2.md)

## Sources

- [MIT 18.103 Fourier Analysis (Fall 2013), Section 1: Fourier Integrals on $L^2(\mathbb{R})$ and $L^1(\mathbb{R})$](../../../../sources/v1/FourierAnalysis.md)
