---
article_id: af_1b15db6e2a9e35da18888a7d
declaration: def
origin: cited
statement: formalized
lean: InvLim
---

# Definition 8.9

Let $(X_i, f_{ij})$ be an inverse system in a concrete category with products. The inverse limit (or projective limit) of $(X_i, f_{ij})$ is the object $X \coloneqq \varprojlim X_i \coloneqq \{x \in \prod_{i \in I} X_i : x_i = f_{ij}(x_j) \text{ for all } i \leq j\} \subseteq \prod_{i \in I} X_i$ (whenever such an object $X$ exists in the category). The restrictions $\pi_i : X \rightarrow X_i$ of the projections $\prod X_i \rightarrow X_i$ satisfy $\pi_i = f_{ij} \circ \pi_j$ for $i \leq j$.

## Depends on

- [Definition 8.8](179-definition-8-8.md)

## Sources

- [MIT 18.785 Number Theory I (Fall 2021), Section 8.1.2](../../../../../sources/v1/NumberTheoryI.md)
