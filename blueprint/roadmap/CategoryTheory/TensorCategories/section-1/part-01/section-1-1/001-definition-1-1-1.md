---
article_id: af_5c8597329624c5897979ed5d
declaration: abbrev
origin: cited
lean: Definition_1_1_1
---

# Definition 1.1.1

A monoidal category is a quintuple $(\mathcal{C}, \otimes, a, \mathbf{1}, \iota)$ where $\mathcal{C}$ is a category, $\otimes \colon \mathcal{C} \times \mathcal{C} \to \mathcal{C}$ is a bifunctor called the tensor product bifunctor, $a \colon (\bullet \otimes \bullet) \otimes \bullet \to \bullet \otimes (\bullet \otimes \bullet)$ is a functorial isomorphism $a_{X,Y,Z} \colon (X \otimes Y) \otimes Z \to X \otimes (Y \otimes Z)$, $X, Y, Z \in \mathcal{C}$, called the associativity constraint (or associativity isomorphism), $\mathbf{1} \in \mathcal{C}$ is an object of $\mathcal{C}$, and $\iota \colon \mathbf{1} \otimes \mathbf{1} \to \mathbf{1}$ is an isomorphism, subject to the following two axioms. 1. The pentagon axiom: the pentagon diagram is commutative for all objects $W, X, Y, Z$ in $\mathcal{C}$. 2. The unit axiom: the functors $L_{\mathbf{1}}$ and $R_{\mathbf{1}}$ of left and right multiplication by $\mathbf{1}$ are equivalences $\mathcal{C} \to \mathcal{C}$. The pair $(\mathbf{1}, \iota)$ is called the unit object of $\mathcal{C}$.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.769 Topics in Lie Theory: Tensor Categories (Spring 2009), Section 1.1](../../../../../../sources/v1/TensorCategories.md)
