---
article_id: af_e16b29dc24695de2a9bb922d
declaration: theorem
origin: cited
statement: formalized
lean: FourierAnalysis.proposition_2_0_2
---

# Proposition 2.0.2 (Class Meeting #16, Section 2)

Let $f \in C_{c}^{\infty}(\mathbb{R}^{n})$, i.e., $f$ is a smooth, compactly supported function. Then $\hat{f}$ is smooth and "rapidly decaying at infinity" in the following sense: for each $N \geq 0$, there exists a constant $C_{N}>0$ such that $|\hat{f}(\xi)| \leq C_{N}(1+|\xi|)^{-N}$. Furthermore, an estimate similar to the above holds (with possibly different constants) for all of the derivatives $|\partial_{\vec{\beta}} \hat{f}(\xi)|$. In particular, $\hat{f} \in L^{1}$: $\|\hat{f}(\xi)\|_{L^{1}} \coloneqq \int_{\mathbb{R}^{n}}|\hat{f}(\xi)| d^{n} \xi\lt \infty$, and similarly for $\partial_{\vec{\beta}} \hat{f}$, where $\vec{\beta}$ is any derivative multi-index.

## Depends on

- [Definition 1.0.1 (Fourier Transform)](069-fourier-transform.md)
- [Definition 1.0.3](071-definition-1-0-3.md)

## Sources

- [MIT 18.152 Introduction to Partial Differential Equations (Fall 2011), Class Meeting #16, Section 2](../../../../../sources/v1/IntroductionToPartialDifferentialEquations.md)
