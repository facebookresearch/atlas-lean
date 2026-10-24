---
article_id: af_85314d9ad9a3d2c9f301c3d6
declaration: theorem
origin: cited
statement: formalized
lean: residue_theorem
---

# Theorem 17'

Let $f$ be analytic except for isolated singularities $a_j$ in a region $\Omega$. Let $\gamma$ be a simple closed curve which has interior contained in $\Omega$ and $a_j \notin \gamma$ (all $j$). Then $$\frac{1}{2\pi i} \int_{\gamma} f(z)\, dz = \sum_{j} \operatorname{Res}_{z=a_j} f(z)$$ where the sum ranges over all $a_j$ inside $\gamma$.

## Depends on

- [Definition 1 (Lecture 14: The Residue Theorem and Application)](019-definition-1.md)

## Proof depends on

- [Definition 2](../lecture-13/015-definition-2.md)
- [Theorem 1 (Cauchy's Theorem)](../lecture-13/016-cauchy-s-theorem.md)

## Sources

- [MIT 18.112 Functions of a Complex Variable (Fall 2008), Lecture 14: The Residue Theorem and Application](../../../../sources/v1/ComplexVariables.md)
