---
article_id: af_a148b0349904bd5f34072611
declaration: theorem
origin: cited
lean: SpectralTheory.compact_selfAdjoint_maximum_principle
---

# Theorem (Maximum principle)

Let $A = A^\ast$ be a self-adjoint compact operator. Then the nonzero eigenvalues of $A$ can be ordered as $|\lambda_1| \geq |\lambda_2| \geq \cdots$ (including multiplicity), such that we have pairwise orthonormal eigenfunctions $\{u_k\}$ for $\lambda_k$, satisfying $|\lambda_j| = \sup_{\substack{||u|| = 1 \\ u \in \operatorname{Span}(u_1, \cdots, u_{j-1})^\perp}} |\langle Au, u \rangle| = |\langle Au_j, u_j \rangle|$. Furthermore, we have $|\lambda_j| \to 0$ as $j \to \infty$ if the sequence of nonzero eigenvalues does not terminate.

## Depends on

- [Definition (May 4, 2021)](../may-4/064-definition.md)

## Sources

- [MIT 18.102 Introduction to Functional Analysis (Spring 2021), May 11, 2021](../../../../../sources/v1/IntroductionToFunctionalAnalysis.md)
