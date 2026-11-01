---
article_id: af_d12e042c83d1e4758ec2c6f9
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: CourantFischer.rayleighQuotient_orthogonal_isLeast
---

# Theorem 23 (Courant-Fischer Formula)

For any $n \times n$ symmetric matrix $A$, $\lambda_1 = \min_{\|x\|=1} x^\top A x = \min_{x \neq 0} \frac{x^\top A x}{x^\top x}$, $\lambda_2 = \min_{\|x\|=1,\, x \perp v_1} x^\top A x = \min_{x \neq 0,\, x \perp v_1} \frac{x^\top A x}{x^\top x}$, $\lambda_{\max} = \max_{\|x\|=1} x^\top A x = \max_{x \neq 0} \frac{x^\top A x}{x^\top x}$.

## Depends on

- [Definition 1 (Lecture 1, Section 2)](../../lecture-1/001-definition-1.md)

## Proof depends on

- [Proposition 2 (Lecture 1, Section 2)](../../lecture-1/002-proposition-2.md)

## Sources

- [MIT 18.409 An Algorithmist's Toolkit (Fall 2009), Lecture 2, Section 7](../../../../../../sources/v1/AnAlgorithmistsToolkit.md)
