---
article_id: af_9f4a3fc21190497687e2766a
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: FourierInversionL2.fourier_L2_equiv
---

# Corollary 4 (Fourier inversion on $L^2$)

Let $\mathcal{G}(f)(x) = \frac{1}{2\pi}\hat{f}(-x)$. Then for all $f \in L^2(\mathbb{R})$, $\mathcal{G} \circ \mathcal{F}(f) = \mathcal{F} \circ \mathcal{G}(f) = f$. Thus, up to the factor $2\pi$, the Fourier transform is an isometry (distance preserving) from $L^2(\mathbb{R})$ to itself.

## Depends on

- [Corollary 2 (Section 1: Fourier Integrals on $L^2(\mathbb{R})$ and $L^1(\mathbb{R})$)](011-corollary-2.md)

## Proof depends on

- [Theorem 1 (Section 1: Fourier Integrals on $L^2(\mathbb{R})$ and $L^1(\mathbb{R})$)](007-theorem-1.md)

## Sources

- [MIT 18.103 Fourier Analysis (Fall 2013), Section 1: Fourier Integrals on $L^2(\mathbb{R})$ and $L^1(\mathbb{R})$](../../../../sources/v1/FourierAnalysis.md)
