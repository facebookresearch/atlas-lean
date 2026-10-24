---
article_id: af_31682f2884a103e7b0c018a5
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: HeatFundamental.leibniz_integral_rule
---

# Proposition 1.1.1 (Differentiating under the integral)

Let $I(a, b)$ be a function on $\mathbb{R} \times \mathbb{R}$. Assume that $\int_{\mathbb{R}}|I(a, b)| da\lt \infty$ for all $b$ belonging to a neighborhood of $b_{0}$ and define $J(b) \coloneqq \int_{\mathbb{R}} I(a, b) da$. Assume that there exists a neighborhood $\mathcal{N}$ of $b_{0}$ such that for almost every $a$, $\partial_{b} I(a, b)$ exists for $b \in \mathcal{N}$. In addition, assume that there exists a function $U(a)$ (defined for almost all $a$) such that for $b \in \mathcal{N}$, we have that $|\partial_{b} I(a, b)| \leq U(a)$ and such that $\int_{\mathbb{R}} U(a) da\lt \infty$. Then $J(b)$ is differentiable near $b_{0}$, and $\partial_{b} J(b)=\int_{\mathbb{R}} \partial_{b} I(a, b) da$.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.152 Introduction to Partial Differential Equations (Fall 2011), Section 1.1](../../../../../sources/v1/IntroductionToPartialDifferentialEquations.md)
