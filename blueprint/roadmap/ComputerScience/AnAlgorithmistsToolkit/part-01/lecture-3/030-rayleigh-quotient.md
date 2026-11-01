---
article_id: af_64c5ba878dfdb2059d811ac3
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: CourantFischer.corollary24_rayleighQuotient
---

# Corollary 2 (Rayleigh Quotient)

Let $G = (V, E)$ be a graph and $L$ be the Laplacian of $G$. The smallest eigenvalue is $\lambda_1 = 0$ with eigenvector $v_1 = \mathbf{1}$. By the Courant-Fischer Formula, $\lambda_2 = \min_{x \neq 0,\, x \perp \mathbf{1}} \frac{\sum_{(i,j) \in E} (x_i - x_j)^2}{\sum_{i \in V} x_i^2}$, and $\lambda_{\max} = \max_{x \neq 0} \frac{\sum_{(i,j) \in E} (x_i - x_j)^2}{\sum_{i \in V} x_i^2}$.

## Depends on

- [Definition 1 (Lecture 1, Section 2)](../lecture-1/001-definition-1.md)

## Proof depends on

- [Proposition 6 (Lecture 1, Section 4)](../lecture-1/006-proposition-6.md)
- [Theorem 23 (Courant-Fischer Formula)](../lecture-2/lecture-2-section-7/028-courant-fischer-formula.md)

## Sources

- [MIT 18.409 An Algorithmist's Toolkit (Fall 2009), Lecture 3, Section 2](../../../../../sources/v1/AnAlgorithmistsToolkit.md)
