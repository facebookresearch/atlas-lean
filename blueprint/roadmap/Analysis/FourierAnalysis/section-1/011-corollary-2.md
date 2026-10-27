---
article_id: af_4b4c1817e5664816e6732d2a
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: L2FourierExtension.fourier_L2_linear_isometry_equiv
---

# Corollary 2 (Section 1: Fourier Integrals on $L^2(\mathbb{R})$ and $L^1(\mathbb{R})$)

Let $f \in L^2(\mathbb{R})$ and let $f_j \in \mathcal{S}(\mathbb{R})$ be such that $\|f - f_j\|_2 \to 0$ as $j \to \infty$. Then $\hat{f}_j$ is a Cauchy sequence in $L^2(\mathbb{R})$ and the limit (in the $L^2$ metric) is independent of the choice of sequence approximating $f$. Thus there is a unique function denoted $\hat{f} \in L^2(\mathbb{R})$ for which $\lim_{j \to \infty} \|\hat{f} - \hat{f}_j\|_2 = 0$. Furthermore, $\|\hat{f}\|_2^2 = 2\pi \|f\|_2^2$.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Corollary 1 (Section 1: Fourier Integrals on $L^2(\mathbb{R})$ and $L^1(\mathbb{R})$)](008-corollary-1.md)

## Sources

- [MIT 18.103 Fourier Analysis (Fall 2013), Section 1: Fourier Integrals on $L^2(\mathbb{R})$ and $L^1(\mathbb{R})$](../../../../sources/v1/FourierAnalysis.md)
