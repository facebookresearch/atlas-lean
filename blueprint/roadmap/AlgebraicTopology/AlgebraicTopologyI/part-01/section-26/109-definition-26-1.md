---
article_id: af_70130260073e7777cfa4e95c
declaration: class
origin: cited
statement: formalized
lean: GradedCoalgebra
---

# Definition 26.1

Let $R$ be a ring. A (graded) coalgebra over $R$ is a (graded) $R$-module $M$ equipped with a "comultiplication" $\Delta \colon M \rightarrow M \otimes_{R} M$ and a "counit" map $\varepsilon \colon M \rightarrow R$ such that the coassociativity and counit diagrams commute. It is commutative if in addition the diagram involving the twist map $\tau(x \otimes y) = (-1)^{|x| \cdot |y|} y \otimes x$ commutes.

## Depends on

- [Definition 20.3](../section-20/080-definition-20-3.md)

## Sources

- [MIT 18.905 Algebraic Topology I (Fall 2016), Section 26](../../../../../sources/v1/AlgebraicTopologyI.md)
