# Cyclic prime-power isogenies correspond to chains without backtracking

For $\ell$ prime to the characteristic, cyclic isogenies of degree $\ell^m$ from a curve and chains of $m$ isogenies of degree $\ell$ without backtracking from it determine each other, and the factorization of a cyclic isogeny into such a chain is unique.

Let $k$ be an algebraically closed field, $\ell$ a prime different from $\operatorname{char}k$, $m\ge 1$, and $E_0$ an elliptic curve over $k$; all curves, isogenies and isomorphisms below are over $k$. Call two chains $(\varphi_i\colon E_{i-1}\to E_i)$ and $(\varphi'_i\colon E'_{i-1}\to E'_i)$ with $E_0=E'_0$ *equivalent* if there are isomorphisms $\iota_i\colon E_i\to E'_i$ with $\iota_0=\mathrm{id}$ and $\varphi'_i\circ\iota_{i-1}=\iota_i\circ\varphi_i$ for all $i$. Then taking composites gives a bijection between

- equivalence classes of chains of $\ell$-isogenies of length $m$ from $E_0$ [without backtracking](isogeny-chain-without-backtracking.md), and
- [cyclic](cyclic-isogeny.md) $\ell^m$-isogenies from $E_0$ up to post-composition with an isomorphism of the target, equivalently cyclic subgroups of order $\ell^m$ of $E_0(k)$.

Over a field that is not algebraically closed the bijection fails as stated: over $\mathbb{R}$, the curve $y^2=x^3+x$ has three subgroups of order $2$ over $\mathbb{C}$ but only one over $\mathbb{R}$, so not every geometric cyclic subgroup is the kernel of an $\mathbb{R}$-rational step.

In particular, if $\varphi_n\circ\cdots\circ\varphi_1=\varphi'_n\circ\cdots\circ\varphi'_1$ for two chains without backtracking from $E_0$ to the same curve, then $\ker(\varphi_i\circ\cdots\circ\varphi_1)=\ker(\varphi'_i\circ\cdots\circ\varphi'_1)$ for every $i$, and the two chains are equivalent with $\iota_n=\mathrm{id}$.

## Depends on

- [Cyclic isogeny](cyclic-isogeny.md)
- [Chain of isogenies without backtracking](isogeny-chain-without-backtracking.md)

## Proof depends on

- [A cyclic isogeny of prime-power degree is a chain without backtracking](cyclic-prime-power-isogeny-factors-without-backtracking.md)
- [A chain without backtracking composes to a cyclic isogeny](non-backtracking-chain-composes-to-cyclic-isogeny.md)
- [Every finite subgroup is the kernel of a separable isogeny](../isogenies-of-elliptic-curves/separable-isogeny-with-prescribed-kernel.md)

## Expansion

The composite of a chain without backtracking is cyclic, and every cyclic isogeny arises; equivalent chains have composites that differ by $\iota_m$. For injectivity, the kernel of the partial composite $\varphi_i\circ\cdots\circ\varphi_1$ is a subgroup of order $\ell^i$ of the cyclic group $C=\ker(\varphi_m\circ\cdots\circ\varphi_1)$, and a cyclic group of order $\ell^m$ has exactly one subgroup of each order $\ell^i$; so the partial kernels are determined by $C$, and separable isogenies with equal kernels differ by isomorphisms, which assemble into the $\iota_i$. This is the uniqueness of the composition series of a cyclic group that Charles, Goren and Lauter invoke. They state their Proposition 1 under the standing assumption $p\equiv 1\pmod{12}$ of their Section 5, which the proof does not use; Costache, Feigon, Lauter, Massierer and Puskás state the correspondence with no congruence condition.

## Sources

- Anamaria Costache, Brooke Feigon, Kristin Lauter, Maike Massierer, Anna Puskás, "Ramanujan graphs in cryptography", in *Research Directions in Number Theory (Women in Numbers IV)*, Association for Women in Mathematics Series 19, Springer (2019) 1–40, [doi:10.1007/978-3-030-19478-9_1](https://doi.org/10.1007/978-3-030-19478-9_1); numbers from arXiv:1806.05709v2, Corollary 4.5.
- Denis X. Charles, Eyal Z. Goren, Kristin E. Lauter, "Cryptographic Hash Functions from Expander Graphs", *Journal of Cryptology* 22 (2009) 93–113, [doi:10.1007/s00145-007-9002-x](https://doi.org/10.1007/s00145-007-9002-x), Proposition 1.
