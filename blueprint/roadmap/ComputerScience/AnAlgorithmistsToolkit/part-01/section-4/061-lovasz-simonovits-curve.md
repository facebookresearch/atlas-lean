---
article_id: af_50e14370f30be1315cdde46a
declaration: def
origin: cited
statement: formalized
lean: LovaszSimonovits.lsCurve
---

# Definition 7 (Lovasz-Simonovits curve)

For a given $\rho$, order the arcs such that $\rho(e_1) \geq \rho(e_2) \geq \cdots \geq \rho(e_{2m})$. We define $I : [0, 2m] \to [0, 1]$ as follows: For each $k \in \{0, \ldots, 2m\}$, $I(k) = \sum_{i=1}^{k} \rho(e_i)$. We extend $I$ to the complete interval by interpolating it piecewise linearly.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.409 An Algorithmist's Toolkit (Fall 2009), Section 4.3](../../../../../sources/v1/AnAlgorithmistsToolkit.md)
