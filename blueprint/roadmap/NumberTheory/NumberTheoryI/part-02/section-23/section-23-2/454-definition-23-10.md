---
article_id: af_7f75d5a7c3c78a65e950c042
declaration: def
origin: cited
statement: formalized
lean: GroupCohomology.standardResolution
---

# Definition 23.10

Let $G$ be a group. The standard resolution of $\mathbb{Z}$ by $G$-modules is the exact sequence of $G$-module homomorphisms $\cdots \longrightarrow \mathbb{Z}[G^{n+1}] \xrightarrow{d_{n}} \mathbb{Z}[G^{n}] \longrightarrow \cdots \xrightarrow{d_{1}} \mathbb{Z}[G] \xrightarrow{d_{0}} \mathbb{Z} \longrightarrow 0$ where the boundary maps $d_{n}$ are defined by $d_{n}(g_{0}, \ldots, g_{n})\coloneqq \sum_{i=0}^{n}(-1)^{i}(g_{0}, \ldots, \hat{g}_{i}, \ldots, g_{n})$ and extended $\mathbb{Z}$-linearly (the notation $\hat{g}_{i}$ means omit $g_{i}$ from the tuple). The map $d_{0}$ sends each $g \in G$ to 1, and extends to the map $\sum_{g} a_{g} g \mapsto \sum_{g} a_{g}$, which is also known as the augmentation map and may be denoted $\varepsilon$.

## Depends on

- [Definition 23.1](../section-23-1/446-definition-23-1.md)

## Sources

- [MIT 18.785 Number Theory I (Fall 2021), Section 23.2](../../../../../../sources/v1/NumberTheoryI.md)
