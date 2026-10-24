---
article_id: af_c251cc8685ff086d8ec14f0d
declaration: def
origin: cited
lean: GlobalConductor.conductorModulus
---

# Definition 22.24

Let $L/K$ be a finite abelian extension of local fields. The conductor $\mathfrak{c}(L/K)$ is defined as follows. If $K$ is archimedean then $\mathfrak{c}(L/K)=1$ when $K \simeq \mathbb{R}$ and $L \simeq \mathbb{C}$ and $\mathfrak{c}(L/K)=0$ otherwise. If $K$ is nonarchimedean and $\mathfrak{p}$ is the maximal ideal of its valuation ring $\mathcal{O}_{K}$, then $\mathfrak{c}(L/K)\coloneqq \min\{n: 1+\mathfrak{p}^{n} \subseteq \mathrm{N}_{L/K}(L^{\times})\}$ (here $1+\mathfrak{p}^{n}$ is a subgroup of $\mathcal{O}_{K}^{\times}$, with $1+\mathfrak{p}^{0}\coloneqq \mathcal{O}_{K}^{\times}$). If $L/K$ is a finite abelian extension of global fields then its conductor is the modulus $\mathfrak{c}(L/K): M_{K} \rightarrow \mathbb{Z}$, $v \mapsto \mathfrak{c}(L_{w}/K_{v})$ where $K_{v}$ is the completion of $K$ at $v$ and $L_{w}$ is the completion of $L$ at a place $w \mid v$. As with any modulus, we may view the finite part of $\mathfrak{c}(L/K)$ as an $\mathcal{O}_{K}$-ideal and the infinite part as a subset of ramified infinite places.

## Depends on

- [Definition 21.2](../../section-21/404-definition-21-2.md)
- [Definition 4.46](../../../part-01/section-4/section-4-3/091-definition-4-46.md)
- [Definition 13.1](../../../part-01/section-13/264-definition-13-1.md)
- [Definition 13.22](../../../part-01/section-13/279-definition-13-22.md)

## Proof depends on

- [Definition 9.1](../../../part-01/section-9/187-definition-9-1.md)

## Sources

- [MIT 18.785 Number Theory I (Fall 2021), Section 22.3](../../../../../../sources/v1/NumberTheoryI.md)
