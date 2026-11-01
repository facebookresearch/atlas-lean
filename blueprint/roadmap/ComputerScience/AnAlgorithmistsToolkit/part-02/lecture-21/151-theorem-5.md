---
article_id: af_7b5c71183975960e5dbfbedf
declaration: theorem
origin: cited
statement: formalized
lean: An_Algorithmists_Toolkit.steepest_descent_error_reduction
---

# Theorem 5 (Lecture 21, Section 4.3)

Let $e_i$ denote the error vector at step $i$ of steepest descent. Let $\{v_j\}_{j=1}^n$ be a normalized eigenbasis of $A$ with corresponding eigenvalues $\lambda_j$, and let $e_i = \sum_j \xi_j v_j$ denote the expansion of $e_i$ with respect to this eigenbasis. Then $\|e_{i+1}\|_A^2 = \|e_i\|_A^2 \left(1 - \frac{(\sum_j \xi_j^2 \lambda_j^2)^2}{(\sum_j \xi_j^2 \lambda_j^3)(\sum_j \xi_j^2 \lambda_j)}\right)$.

## Depends on

- [Definition 4 (Lecture 21, Section 4.3)](150-definition-4.md)
- [Definition 1 (Lecture 1, Section 2)](../../part-01/lecture-1/001-definition-1.md)

## Sources

- [MIT 18.409 An Algorithmist's Toolkit (Fall 2009), Lecture 21, Section 4.3](../../../../../sources/v1/AnAlgorithmistsToolkit.md)
