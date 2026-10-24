---
article_id: af_3ab10831cf0dc57f952c4639
declaration: class
origin: cited
statement: formalized
lean: CategoryTheory.LeftModuleCategory'
---

# Definition 2.1.1

A left module category over $\mathcal{C}$ is a category $\mathcal{M}$ equipped with an action (or tensor product) bifunctor $\otimes^{\mathcal{M}} \colon \mathcal{C} \times \mathcal{M} \to \mathcal{M}$ and a functorial associativity isomorphism (or constraint) $a^{\mathcal{M}} \colon (\bullet \otimes \bullet) \otimes^{\mathcal{M}} \bullet \to \bullet \otimes (\bullet \otimes^{\mathcal{M}} \bullet)$, such that the functor $\mathbf{1} \otimes^{\mathcal{M}} \colon \mathcal{M} \to \mathcal{M}$ is an autoequivalence, and $a^{\mathcal{M}}$ satisfies the pentagon relation.

## Depends on

- [Definition 1.1.1](../../section-1/part-01/section-1-1/001-definition-1-1-1.md)

## Sources

- [MIT 18.769 Topics in Lie Theory: Tensor Categories (Spring 2009), Section 2.1](../../../../../sources/v1/TensorCategories.md)
