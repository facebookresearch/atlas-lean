---
article_id: af_c68c9bce4def715232539240
declaration: abbrev
origin: cited
statement: formalized
lean: DirectedSystems.DirectedSystemFunctor
---

# Definition 23.4

Let $\mathcal{I}$ be a directed set. An $\mathcal{I}$-directed system in a category $\mathcal{C}$ is a functor $\mathcal{I} \rightarrow \mathcal{C}$. This means that for every $i \in \mathcal{I}$ we are given an object $X_{i} \in \mathcal{C}$, and for every $i \leq j$ we are given a map $f_{i,j} \colon X_{i} \rightarrow X_{j}$, in such a way that $f_{i,i} = 1_{X_{i}}$ and if $i \leq j \leq k$ then $f_{i,k} = f_{j,k} \circ f_{i,j} \colon X_{i} \rightarrow X_{k}$.

## Depends on

- [Definition 3.1](../chapter-1/chapter-1-section-3/008-definition-3-1.md)
- [Definition 3.4](../chapter-1/chapter-1-section-3/010-definition-3-4.md)
- [Definition 23.2](088-definition-23-2.md)

## Sources

- [MIT 18.905 Algebraic Topology I (Fall 2016), Section 23](../../../../../sources/v1/AlgebraicTopologyI.md)
