---
article_id: af_3494db1292fa7bed27bb07ca
declaration: structure
origin: cited
statement: formalized
lean: LLL.IsReducedBasis
---

# Definition 6 (Reduced bases)

Let $\{b_1, \ldots, b_n\}$ be a basis for a lattice $L$ and let $M$ be its Gram-Schmidt matrix. Then $\{b_1, \ldots, b_n\}$ is a reduced basis if it meets the following two conditions: (1) All the non-diagonal entries of $M$ satisfy $|\mu_{ik}| \leq 1/2$. (2) For each $i$, $\|\pi_{S_i} b_i\|^2 \leq \frac{4}{3}\|\pi_{S_i} b_{i+1}\|^2$, where $S_i$ is the subspace orthogonal to $\operatorname{span}(b_1, \ldots, b_{i-1})$.

## Depends on

- [Definition (Lattice)](../lecture-18/130-lattice.md)

## Sources

- [MIT 18.409 An Algorithmist's Toolkit (Fall 2009), Lecture 19, Section 4.3](../../../../../sources/v1/AnAlgorithmistsToolkit.md)
