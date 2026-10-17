---
article_id: af_cdd7e5816773f14a99caf3d1
declaration: structure
origin: cited
statement: formalized
lean: TensorCategories.def_1_4_1_MonoidalFunctor
---

# Definition 1.4.1

Let $(\mathcal{C}, \otimes, \mathbf{1}, a, \iota)$ and $(\mathcal{C}', \otimes', \mathbf{1}', a', \iota')$ be two monoidal categories. A monoidal functor from $\mathcal{C}$ to $\mathcal{C}'$ is a pair $(F, J)$ where $F \colon \mathcal{C} \to \mathcal{C}'$ is a functor, and $J = \{J_{X,Y} \colon F(X) \otimes' F(Y) \to F(X \otimes Y) \mid X, Y \in \mathcal{C}\}$ is a natural isomorphism, such that $F(\mathbf{1})$ is isomorphic to $\mathbf{1}'$, and the monoidal structure axiom diagram is commutative for all $X, Y, Z \in \mathcal{C}$. A monoidal functor $F$ is said to be an equivalence of monoidal categories if it is an equivalence of ordinary categories.

## Depends on

- [Definition 1.1.1](../section-1-1/001-definition-1-1-1.md)

## Sources

- [MIT 18.769 Topics in Lie Theory: Tensor Categories (Spring 2009), Section 1.4](../../../../../../sources/v1/TensorCategories.md)
