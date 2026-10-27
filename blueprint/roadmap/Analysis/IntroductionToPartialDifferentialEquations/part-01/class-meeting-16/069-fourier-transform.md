---
article_id: af_b44bb9c6420ee40f7aa4b8cb
declaration: def
origin: cited
statement: formalized
lean: FourierAnalysis.fourierTransformND
---

# Definition 1.0.1 (Fourier Transform)

Let $f \in L^{1}(\mathbb{R}^{n})$, i.e., $\int_{\mathbb{R}^{n}}|f(x)| d^{n} x\lt \infty$. The Fourier transform of $f$ is denoted by $\hat{f}$, and it is a new function of the frequency variable $\xi \in \mathbb{R}^{n}$. It is defined for each frequency $\xi$ as follows: $\hat{f}(\xi) \coloneqq \int_{\mathbb{R}^{n}} f(x) e^{-2 \pi i \xi \cdot x} d^{n} x$ where $\cdot$ denotes the Euclidean dot product, i.e., if $x=(x^{1}, \cdots, x^{n})$ and $\xi=(\xi^{1}, \cdots, \xi^{n})$, then $\xi \cdot x \coloneqq \sum_{j=1}^{n} \xi^{j} x^{j}$. In the above formula, recall that if $r$ is a real number, then $e^{ir}=\sin r+i \cos r$.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.152 Introduction to Partial Differential Equations (Fall 2011), Class Meeting #16, Section 1](../../../../../sources/v1/IntroductionToPartialDifferentialEquations.md)
