# Number of chains of l-isogenies without backtracking

From a fixed elliptic curve, there are $\ell^m+\ell^{m-1}$ chains of $m$ isogenies of degree $\ell$ without backtracking, counted up to isomorphisms of the intermediate and final curves, when $\ell$ is prime to the characteristic.

Let $E_0$ be an elliptic curve over an algebraically closed field $k$, $\ell$ a prime different from $\operatorname{char}k$, and $m\ge 1$. The number of equivalence classes, in the sense of the correspondence with cyclic isogenies, of chains of $\ell$-isogenies of length $m$ from $E_0$ [without backtracking](isogeny-chain-without-backtracking.md) is

$$
\ell^m+\ell^{m-1}=(\ell+1)\,\ell^{m-1} .
$$

## Depends on

- [Chain of isogenies without backtracking](isogeny-chain-without-backtracking.md)
- [Cyclic prime-power isogenies correspond to chains without backtracking](cyclic-isogenies-correspond-to-non-backtracking-chains.md)

## Proof depends on

- [Counting subgroups of prime-power order in the torsion of an elliptic curve](number-of-cyclic-subgroups-of-prime-power-torsion.md)

## Expansion

By the correspondence, these classes are in bijection with the cyclic subgroups of order $\ell^m$ of $E_0$, of which there are $\ell^m+\ell^{m-1}$. Directly: the first step has $\ell+1$ choices of kernel, and every later step has $\ell$, since exactly one of the $\ell+1$ subgroups of order $\ell$ of $E_i$ is the kernel of $\hat\varphi_i$; this is the $(\ell+1)$-regular tree of depth $m$ in which isomorphic curves are not identified.

## Sources

- Anamaria Costache, Brooke Feigon, Kristin Lauter, Maike Massierer, Anna Puskás, "Ramanujan graphs in cryptography", in *Research Directions in Number Theory (Women in Numbers IV)*, Association for Women in Mathematics Series 19, Springer (2019) 1–40, [doi:10.1007/978-3-030-19478-9_1](https://doi.org/10.1007/978-3-030-19478-9_1); numbers from arXiv:1806.05709v2, Theorem 4.9 and the paragraph after it (the tree count).
