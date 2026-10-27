---
article_id: af_70f1f1f2d0e83d9e8d904005
declaration: def
origin: cited
statement: formalized
lean: FourierAnalysis.complexL2InnerND
---

# Definition 1.0.5 (Inner product for complex-valued functions)

Let $f$ and $g$ be complex-valued functions defined on $\mathbb{R}^{n}$. We define their complex inner product by $\langle f, g\rangle \coloneqq \int_{\mathbb{R}^{n}} f(x) \bar{g}(x) d^{n} x$, where $\bar{g}$ denotes the complex conjugate of $g$. That is, if $g(x)=u(x)+i v(x)$, where $u$ and $v$ are real-valued, then $\bar{g}(x) \coloneqq u(x)-i v(x)$. We also define the norm of $f$ by $\|f\| \coloneqq \langle f, f\rangle^{1/2} \coloneqq \left(\int_{\mathbb{R}^{n}}|f(x)|^{2} d^{n} x\right)^{1/2}$.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.152 Introduction to Partial Differential Equations (Fall 2011), Class Meeting #16, Section 1](../../../../../sources/v1/IntroductionToPartialDifferentialEquations.md)
