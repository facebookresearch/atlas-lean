# Two different equal-length paths between supersingular curves give a non-scalar endomorphism

For $p\equiv1\pmod{12}$, two different chains of $n$ isogenies of degree $\ell$ without backtracking, from one supersingular curve to isomorphic curves, give two isogenies of degree $\ell^n$ with different kernels and an endomorphism of degree $\ell^{2n}$ of the first curve that is not $\pm[\ell^n]$.

Let $p$ be a prime with $p\equiv1\pmod{12}$, $\ell\ne p$ a prime, $n\ge1$, and $\bar{\mathbb{F}}_p$ an algebraic closure of $\mathbb{F}_p$; all curves, isogenies and isomorphisms are over $\bar{\mathbb{F}}_p$. Let $E_1$ be a [supersingular](../supersingular-elliptic-curves/is-supersingular.md) elliptic curve and let $(\varphi_i)$ and $(\varphi'_i)$ be two chains of $\ell$-isogenies of length $n$ from $E_1$, both [without backtracking](isogeny-chain-without-backtracking.md), ending at curves isomorphic to a curve $E_2$, and not equivalent in the sense of the [correspondence with cyclic isogenies](cyclic-isogenies-correspond-to-non-backtracking-chains.md). Composing each chain with an isomorphism of its last curve onto $E_2$ gives isogenies $f_1,f_2\colon E_1\to E_2$. Then:

1. $f_1$ and $f_2$ are cyclic isogenies of degree $\ell^n$ with $\ker f_1\ne\ker f_2$;
2. $\alpha=\hat f_2\circ f_1$ is an endomorphism of $E_1$ of degree $\ell^{2n}$, where $\hat f_2$ is the [dual](../isogenies-of-elliptic-curves/dual-isogeny.md) of $f_2$, and $\alpha\ne\pm[\ell^n]$; since $\operatorname{Aut}(E_1)=\{\pm1\}$, $\alpha$ is not an automorphism composed with $[\ell^n]$.

This is the content of Charles, Goren and Lauter's Theorem 1 (a collision of their hash, that is, two different paths of the same length between two vertices of the supersingular $\ell$-isogeny graph, solves their Problems 1 and 2), stated for the paths. Nothing here asserts that such paths are hard to find.

## Depends on

- [Supersingular elliptic curves](../supersingular-elliptic-curves/is-supersingular.md)
- [Chain of isogenies without backtracking](isogeny-chain-without-backtracking.md)
- [Cyclic prime-power isogenies correspond to chains without backtracking](cyclic-isogenies-correspond-to-non-backtracking-chains.md)
- [Existence and uniqueness of the dual isogeny](../isogenies-of-elliptic-curves/dual-isogeny.md)

## Proof depends on

- [A chain without backtracking composes to a cyclic isogeny](non-backtracking-chain-composes-to-cyclic-isogeny.md)
- [Degrees of isogenies multiply under composition](../isogenies-of-elliptic-curves/degree-is-multiplicative.md)
- [Multiplication by m has degree m squared](../isogenies-of-elliptic-curves/degree-of-multiplication-by-m.md)
- [Supersingular curves have only the automorphisms plus or minus one when p is 1 mod 12](../supersingular-elliptic-curves/supersingular-automorphisms-when-p-is-one-mod-twelve.md)

## Expansion

The composites are cyclic of degree $\ell^n$, and composing with an isomorphism of the target does not change the kernel. If $\ker f_1=\ker f_2$, the correspondence would make the two chains equivalent; so the kernels differ, which is item 1 and is Charles, Goren and Lauter's Proposition 1. For item 2, $\deg\alpha=\deg\hat f_2\deg f_1=\ell^{2n}$. If $\alpha=[m]$, then $m^2=\ell^{2n}$, so $m=\pm\ell^n$; composing with $f_2$ and using $f_2\circ\hat f_2=[\ell^n]$ gives $[\ell^n]\circ f_1=[\pm\ell^n]\circ f_2$, so $[\ell^n]\circ(f_1\mp f_2)=0$, and since $[\ell^n]$ has finite kernel and a nonzero isogeny is surjective, $f_1=\pm f_2$, whose kernels agree, a contradiction. The same argument excludes $\pm[\ell^n]$ even though $f_1$ and $-f_1$ are different maps: the hypothesis is on kernels, not maps.

Charles, Goren and Lauter, in the proof of their Theorem 1, write the endomorphism as $\phi_1\circ\hat\phi_2$ and call it an endomorphism of $E_1$; that composite is an endomorphism of $E_2$, and $\hat\phi_2\circ\phi_1$ is the endomorphism of $E_1$. They state their results for supersingular curves over $\mathbb{F}_{p^2}$ with the graph of isomorphism classes over $\bar{\mathbb{F}}_p$; this page states them for maps over $\bar{\mathbb{F}}_p$, which is what their proof uses. Equality of $j$-invariants gives isomorphisms over $\bar{\mathbb{F}}_p$, not over $\mathbb{F}_{p^2}$.

## Sources

- Denis X. Charles, Eyal Z. Goren, Kristin E. Lauter, "Cryptographic Hash Functions from Expander Graphs", *Journal of Cryptology* 22 (2009) 93–113, [doi:10.1007/s00145-007-9002-x](https://doi.org/10.1007/s00145-007-9002-x), Proposition 1, Problems 1 and 2, Theorem 1 and its proof, Section 5.3.3.
- Anamaria Costache, Brooke Feigon, Kristin Lauter, Maike Massierer, Anna Puskás, "Ramanujan graphs in cryptography", in *Research Directions in Number Theory (Women in Numbers IV)*, Association for Women in Mathematics Series 19, Springer (2019) 1–40, [doi:10.1007/978-3-030-19478-9_1](https://doi.org/10.1007/978-3-030-19478-9_1); numbers from arXiv:1806.05709v2, Corollary 4.5.
