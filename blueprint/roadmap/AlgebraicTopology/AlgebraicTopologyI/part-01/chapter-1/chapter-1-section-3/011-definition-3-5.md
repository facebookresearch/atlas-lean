---
article_id: af_e4b4ba3541474ac0cdb68f24
declaration: abbrev
origin: cited
statement: formalized
lean: AlgebraicTopologyI.NatTrans
---

# Definition 3.5

Let $F, G \colon \mathcal{C} \rightarrow \mathcal{D}$ be two functors. A natural transformation or natural map $\theta \colon F \rightarrow G$ consists of maps $\theta_{X} \colon F(X) \rightarrow G(X)$ for all $X \in \operatorname{ob}(\mathcal{C})$ such that for all $f \colon X \rightarrow Y$ the following diagram commutes: $G(f) \circ \theta_X = \theta_Y \circ F(f)$.

## Depends on

- [Definition 3.4](010-definition-3-4.md)

## Sources

- [MIT 18.905 Algebraic Topology I (Fall 2016), Chapter 1, Section 3](../../../../../../sources/v1/AlgebraicTopologyI.md)
