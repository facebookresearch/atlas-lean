---
article_id: af_14cb1aa62b951e8703f053dd
declaration: structure
origin: cited
statement: formalized
lean: LLL.IsReducedBasis
---

# Definition 1 (Reduced Basis)

Let $\{b_1, \ldots, b_n\}$ be a basis for a lattice $L$ and let $M$ be its GS matrix. $\{b_1, \ldots, b_n\}$ is a reduced basis if it meets the following two conditions: Condition 1: all the non-diagonal entries of $M$ satisfy $|\mu_{ik}| \leq 1/2$. Condition 2: for each $i$, $\|\pi_{S_i} b_i\|^2 \leq \frac{4}{3}\|\pi_{S_i} b_{i+1}\|^2$, where $S_i$ is the orthogonal complement of $\operatorname{span}(b_1, \ldots, b_{i-1})$, and $\pi_{S_i}$ is the projection operator to $S_i$.

## Depends on

- [Definition (Lattice)](../lecture-18/130-lattice.md)

## Sources

- [MIT 18.409 An Algorithmist's Toolkit (Fall 2009), Lecture 20, Section 2.1](../../../../../sources/v1/AnAlgorithmistsToolkit.md)
