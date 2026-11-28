# Entropic matroids

A matroid is entropic when its rank function is a positive multiple of the joint entropy function of a family of discrete random variables indexed by its ground set.

Let $M$ be a finite [matroid](matroids-given-by-rank-functions.md) $M$ with ground set $E$ and rank function $r$ (in Mathlib, a `Matroid` with `Matroid.Finite`, and $r$ given by `Matroid.eRk`). $M$ is *entropic* if there are random variables $(X_e)_{e \in E}$ on a common discrete probability space, so that each $X_S$ below takes countably many values, and a real number $\lambda > 0$ such that

$$
r(S) = \lambda\, H(X_S) \qquad \text{for all } S \subseteq E,
$$

where $X_S$ is the tuple $(X_e)_{e \in S}$ and $H(X_S)$ is its joint entropy, as in Section 2.2 of the source:

$$
H(X_S) = -\sum_{\omega} P_S(\omega) \log_2 P_S(\omega) \in [0, \infty],
$$

the sum running over the countably many values $\omega$ of $X_S$, with law $P_S$, and $H(X_S) = \infty$ when it diverges. The values need not be finite in number: a single variable taking the value $n \ge 1$ with probability $2^{-n}$ has entropy $2$ and satisfies the identity for the one-element matroid of rank $1$ with $\lambda = 1/2$. When every $X_e$ takes finitely many values this is the [Shannon entropy](../../../InformationTheory/entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/shannon-entropy.md) of a distribution on a finite type.

## Depends on

- [Matroids](matroids-given-by-rank-functions.md)
- [Shannon entropy](../../../InformationTheory/entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/shannon-entropy.md)

## Proof depends on

None.

## Expansion

Every multilinear matroid is entropic, and entropic matroids coincide with the secret sharing matroids of Brickell and Davenport, as the source recalls.

## Sources

- L. Kühne and G. Yashfe, "On entropic and almost multilinear representability of matroids", *Duke Mathematical Journal* 175 (2026), no. 8, 1363–1451, doi:10.1215/00127094-2025-0047; read as arXiv:2206.03465v3, <https://arxiv.org/abs/2206.03465v3>: Section 2.2, Definition 2.3 and Problem 1.1 of arXiv:2206.03465v3.
