---
article_id: af_4d0c8e00ecedfb07c40eb731
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: CourantFischer.corollary24_rayleighQuotient
---

# Corollary 24 (Rayleigh Quotient)

Letting $G = (V, E)$ be a graph with Laplacian $L_G$, $\lambda_1 = 0$ with $v_1 = \mathbf{1}$, $\lambda_2 = \min_{x \perp v_1,\, x \neq 0} \frac{x^\top L_G x}{x^\top x} = \min_{\sum x_i = 0,\, x \neq 0} \frac{\sum_{(i,j) \in E} (x_i - x_j)^2}{\sum_{i \in V} x_i^2}$, and $\lambda_{\max} = \max_{x \neq 0} \frac{x^\top L_G x}{x^\top x} = \max_{x \neq 0} \frac{\sum_{(i,j) \in E} (x_i - x_j)^2}{\sum_{i \in V} x_i^2}$.

## Depends on

- [Definition 1 (Lecture 1, Section 2)](../lecture-1/001-definition-1.md)

## Proof depends on

- [Proposition 6 (Lecture 1, Section 4)](../lecture-1/006-proposition-6.md)
- [Theorem 23 (Courant-Fischer Formula)](../lecture-2/lecture-2-section-7/028-courant-fischer-formula.md)

## Sources

- [MIT 18.409 An Algorithmist's Toolkit (Fall 2009), Section 7](../../../../../sources/v1/AnAlgorithmistsToolkit.md)
