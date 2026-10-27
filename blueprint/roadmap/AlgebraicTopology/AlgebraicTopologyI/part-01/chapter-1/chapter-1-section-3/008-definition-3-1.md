---
article_id: af_c18f15597c621478ec853f4a
declaration: abbrev
origin: cited
statement: formalized
lean: AlgebraicTopologyI.Category
---

# Definition 3.1

A category $\mathcal{C}$ consists of the following data: a class $\operatorname{ob}(\mathcal{C})$ of objects; for every pair of objects $X$ and $Y$, a set of morphisms $\mathcal{C}(X, Y)$; for every object $X$ an identity morphism $1_{X} \in \mathcal{C}(X, X)$; and for every triple of objects $X, Y, Z$, a composition map $\mathcal{C}(X, Y) \times \mathcal{C}(Y, Z) \rightarrow \mathcal{C}(X, Z)$, written $(f, g) \mapsto g \circ f$. These data are required to satisfy the following: $1_{Y} \circ f = f$, and $f \circ 1_{X} = f$; composition is associative: $(h \circ g) \circ f = h \circ (g \circ f)$.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.905 Algebraic Topology I (Fall 2016), Chapter 1, Section 3](../../../../../../sources/v1/AlgebraicTopologyI.md)
