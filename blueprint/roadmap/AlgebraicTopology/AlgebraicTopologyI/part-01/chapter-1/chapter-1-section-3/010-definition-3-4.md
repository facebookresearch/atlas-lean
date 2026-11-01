---
article_id: af_b1cb268df63b913ad8069060
declaration: abbrev
origin: cited
statement: formalized
lean: AlgebraicTopologyI.Functor
---

# Definition 3.4

Let $\mathcal{C}, \mathcal{D}$ be categories. A functor $F \colon \mathcal{C} \rightarrow \mathcal{D}$ consists of the data of an assignment $F \colon \operatorname{ob}(\mathcal{C}) \rightarrow \operatorname{ob}(\mathcal{D})$, and for all $X, Y \in \operatorname{ob}(\mathcal{C})$, a function $F \colon \mathcal{C}(X, Y) \rightarrow \mathcal{D}(F(X), F(Y))$. These data are required to satisfy: for all $X \in \operatorname{ob}(\mathcal{C})$, $F(1_{X}) = 1_{F(X)} \in \mathcal{D}(F(X), F(X))$, and for all composable pairs of morphisms $f, g$ in $\mathcal{C}$, $F(g \circ f) = F(g) \circ F(f)$.

## Depends on

- [Definition 3.1](008-definition-3-1.md)

## Sources

- [MIT 18.905 Algebraic Topology I (Fall 2016), Chapter 1, Section 3](../../../../../../sources/v1/AlgebraicTopologyI.md)
