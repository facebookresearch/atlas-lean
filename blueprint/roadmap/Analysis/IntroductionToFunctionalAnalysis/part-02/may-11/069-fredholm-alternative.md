---
article_id: af_74701b27eab276e52e589c10
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: SpectralTheory.fredholm_alternative_full
---

# Theorem (Fredholm alternative)

Let $A = A^\ast \in \mathcal{B}(H)$ be a self-adjoint compact operator, and let $\lambda \in \mathbb{R} \setminus \{0\}$. Then $\operatorname{Range}(A - \lambda)$ is closed, meaning that $\operatorname{Range}(A - \lambda) = (\operatorname{Range}(A-\lambda)^\perp)^\perp = \operatorname{Null}(A - \lambda)^\perp$. Thus, either $A - \lambda$ is bijective, or the nullspace of $A - \lambda$ (the eigenspace corresponding to $\lambda$) is nontrivial and finite-dimensional.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Proposition (April 22, 2021)](../../part-01/april-22/058-proposition.md)

## Sources

- [MIT 18.102 Introduction to Functional Analysis (Spring 2021), May 11, 2021](../../../../../sources/v1/IntroductionToFunctionalAnalysis.md)
