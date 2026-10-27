---
article_id: af_de7c76cf7b5c4c3640121f94
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: FourierAnalysis.plancherel_theorem_full
---

# Theorem 4.2 (The Plancherel theorem)

Suppose that $f, g: \mathbb{R}^{n} \rightarrow \mathbb{C}$ are continuous functions, that $f, g \in L^{1} \cap L^{2}$, and that $\hat{f}, \hat{g} \in L^{1}$. Then $\hat{f}, \hat{g} \in L^{2}$, and $\langle f, g\rangle = \langle\hat{f}, \hat{g}\rangle$, i.e., the Fourier transform preserves the $L^{2}$ inner product. In particular, by setting $f=g$, it follows that $\|f\|_{L^{2}} = \|\hat{f}\|_{L^{2}}$.

## Depends on

- [Definition 1.0.5 (Inner product for complex-valued functions)](../class-meeting-16/073-inner-product-for-complex-valued-functio.md)
- [Definition 1.0.1 (Fourier Transform)](../class-meeting-16/069-fourier-transform.md)

## Proof depends on

- [Definition 1.0.2 (Inverse Fourier transform)](../class-meeting-16/070-inverse-fourier-transform.md)

## Sources

- [MIT 18.152 Introduction to Partial Differential Equations (Fall 2011), Section 4 (Fourier Inversion and the Plancherel Theorem)](../../../../../sources/v1/IntroductionToPartialDifferentialEquations.md)
