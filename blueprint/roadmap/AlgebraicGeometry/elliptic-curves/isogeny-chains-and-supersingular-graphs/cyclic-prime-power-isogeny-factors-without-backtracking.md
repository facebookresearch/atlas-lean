# A cyclic isogeny of prime-power degree is a chain without backtracking

A cyclic isogeny of degree $\ell^m$, with $\ell$ prime to the characteristic, is the composite of a chain of $m$ isogenies of degree $\ell$ without backtracking, obtained from the subgroups of its kernel.

Let $k$ be an algebraically closed field, $\ell$ a prime different from $\operatorname{char}k$, $m\ge 1$, and $\varphi\colon E_0\to E$ a [cyclic](cyclic-isogeny.md) $\ell^m$-isogeny over $k$ with kernel $\langle P_0\rangle$. Then there is a chain of $\ell$-isogenies $\varphi_i\colon E_{i-1}\to E_i$, $1\le i\le m$, with $E_m=E$, [without backtracking](isogeny-chain-without-backtracking.md), such that

$$
\varphi=\varphi_m\circ\varphi_{m-1}\circ\cdots\circ\varphi_1,\qquad \ker(\varphi_i\circ\cdots\circ\varphi_1)=\langle\ell^{m-i}P_0\rangle\quad(1\le i\le m).
$$

Rational version. Let $E_0$, $E$ and $\varphi$ be defined over a finite field $\mathbb{F}_q$ of characteristic different from $\ell$, with $P_0\in E_0(\mathbb{F}_q)$. Then the curves $E_1,\dots,E_{m-1}$ and the isogenies $\varphi_1,\dots,\varphi_m$ can be chosen defined over $\mathbb{F}_q$.

## Depends on

- [Cyclic isogeny](cyclic-isogeny.md)
- [Chain of isogenies without backtracking](isogeny-chain-without-backtracking.md)

## Proof depends on

- [Every finite subgroup is the kernel of a separable isogeny](../isogenies-of-elliptic-curves/separable-isogeny-with-prescribed-kernel.md)
- [An isogeny factors through a separable isogeny with contained kernel](../isogenies-of-elliptic-curves/factorization-through-a-separable-isogeny.md)
- [Vélu's formulas for the quotient by a finite subgroup](../isogenies-of-elliptic-curves/velu-formulas.md)
- [Degrees of isogenies multiply under composition](../isogenies-of-elliptic-curves/degree-is-multiplicative.md)
- [Structure of the prime-power torsion of an elliptic curve](../isogenies-of-elliptic-curves/structure-of-prime-power-torsion.md)

## Expansion

Put $P_i=\varphi_i(P_{i-1})$ and let $\varphi_i$ be the separable isogeny with kernel $\langle\ell^{m-i}P_{i-1}\rangle$, a group of order $\ell$. By induction $\varphi_i\circ\cdots\circ\varphi_1$ has kernel $\langle\ell^{m-i}P_0\rangle$; for $i=m$ the composite has the same kernel as $\varphi$, so after composing $\varphi_m$ with an isomorphism it equals $\varphi$. If the chain backtracked at step $i$, then $\varphi_{i+1}\circ\varphi_i$ would have kernel $E_{i-1}[\ell]$, so $\ker\varphi$ would contain $E_0[\ell]\cong(\mathbb{Z}/\ell)^2$, which a cyclic group cannot.

Rational version: each $P_i$ is $\mathbb{F}_q$-rational, so Vélu's formulas give the quotient isogenies $\varphi_1,\dots,\varphi_{m-1}$ and their targets over $\mathbb{F}_q$. The Vélu quotient $\psi$ of $E_{m-1}$ by $\langle P_{m-1}\rangle$ is also over $\mathbb{F}_q$, and $\varphi$ and $\psi\circ\varphi_{m-1}\circ\cdots\circ\varphi_1$ are separable over $\mathbb{F}_q$ with the same kernel, so the isomorphism between their targets is defined over $\mathbb{F}_q$ by the factorization page; composing it with $\psi$ gives $\varphi_m$ over $\mathbb{F}_q$. Costache, Feigon, Lauter, Massierer and Puskás make the same remark through Vélu's formulas. Charles, Goren and Lauter describe the factorization as a Jordan–Hölder series of the cyclic kernel, which is unique.

## Sources

- Anamaria Costache, Brooke Feigon, Kristin Lauter, Maike Massierer, Anna Puskás, "Ramanujan graphs in cryptography", in *Research Directions in Number Theory (Women in Numbers IV)*, Association for Women in Mathematics Series 19, Springer (2019) 1–40, [doi:10.1007/978-3-030-19478-9_1](https://doi.org/10.1007/978-3-030-19478-9_1); numbers from arXiv:1806.05709v2, Lemma 4.2 and Remark 4.3.
- Denis X. Charles, Eyal Z. Goren, Kristin E. Lauter, "Cryptographic Hash Functions from Expander Graphs", *Journal of Cryptology* 22 (2009) 93–113, [doi:10.1007/s00145-007-9002-x](https://doi.org/10.1007/s00145-007-9002-x), proof of Proposition 1.
