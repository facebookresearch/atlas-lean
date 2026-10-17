---
article_id: af_d8de7257a37f3e43bbf590ce
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: SchwartzFourierInversion.fourier_inversion
---

# Theorem 1 (Section 1: Fourier Integrals on $L^2(\mathbb{R})$ and $L^1(\mathbb{R})$)

If $f \in \mathcal{S}(\mathbb{R})$, then $\hat{f} \in \mathcal{S}(\mathbb{R})$ and $f(x) = \frac{1}{2\pi} \int_{-\infty}^{\infty} \hat{f}(\xi) e^{ix\xi} \, d\xi$. Thus the inverse operator to the Fourier transform is given by $\check{g}(x) = \frac{1}{2\pi} \int_{-\infty}^{\infty} g(\xi) e^{ix\xi} \, d\xi = \frac{1}{2\pi} \hat{g}(-x)$.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.103 Fourier Analysis (Fall 2013), Section 1: Fourier Integrals on $L^2(\mathbb{R})$ and $L^1(\mathbb{R})$](../../../../sources/v1/FourierAnalysis.md)
