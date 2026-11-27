# Entropic matroids

A matroid is entropic when its rank function is a positive multiple of the joint entropy function of a family of discrete random variables indexed by its ground set.

Let $M = (E, r)$ be a [matroid](matroids-given-by-rank-functions.md). $M$ is *entropic* if there are discrete random variables $(X_e)_{e \in E}$ on a common probability space and a real number $\lambda > 0$ such that

$$
r(S) = \lambda\, H(X_S) \qquad \text{for all } S \subseteq E,
$$

where $X_S$ is the tuple $(X_e)_{e \in S}$ and $H$ is the [Shannon entropy](../../../InformationTheory/entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/shannon-entropy.md) of its distribution.

## Depends on

- [Matroids given by rank functions](matroids-given-by-rank-functions.md)
- [Shannon entropy](../../../InformationTheory/entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/shannon-entropy.md)

## Proof depends on

None.

## Expansion

Every multilinear matroid is entropic, and entropic matroids coincide with the secret sharing matroids of Brickell and Davenport, as the source recalls.

## Sources

- L. Kühne and G. Yashfe, "On entropic and almost multilinear representability of matroids", *Duke Mathematical Journal* 175 (2026), no. 8, 1363–1451, doi:10.1215/00127094-2025-0047; read as arXiv:2206.03465v3, <https://arxiv.org/abs/2206.03465v3>: Definition 2.3 and Problem 1.1 of arXiv:2206.03465v3.
