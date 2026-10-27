---
article_id: af_bed199fd2382e716f4e92549
declaration: abbrev
origin: cited
statement: formalized
lean: CategoryTheory.Definition_2_2_1
---

# Definition 2.2.1

Let $\mathcal{M}_1$ and $\mathcal{M}_2$ be two module categories over $\mathcal{C}$. A module functor from $\mathcal{M}_1$ to $\mathcal{M}_2$ is a pair $(F, s)$ where $F \colon \mathcal{M}_1 \to \mathcal{M}_2$ is a functor, and $s$ is a natural isomorphism $s_{X,M} \colon F(X \otimes M) \to X \otimes F(M)$ such that the appropriate diagrams commute. A module equivalence $F \colon \mathcal{M}_1 \to \mathcal{M}_2$ of $\mathcal{C}$-module categories is a module functor $(F, s)$ from $\mathcal{M}_1$ to $\mathcal{M}_2$ such that $F$ is an equivalence of categories.

## Depends on

- [Definition 2.1.1](../section-2-1/174-definition-2-1-1.md)

## Sources

- [MIT 18.769 Topics in Lie Theory: Tensor Categories (Spring 2009), Section 2.2](../../../../../sources/v1/TensorCategories.md)
