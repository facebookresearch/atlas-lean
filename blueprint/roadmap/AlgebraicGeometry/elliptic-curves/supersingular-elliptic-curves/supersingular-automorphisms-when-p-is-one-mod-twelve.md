# Supersingular curves have only the automorphisms plus or minus one when p is 1 mod 12

When $p\equiv1\pmod{12}$, the curves with $j=0$ and $j=1728$ are ordinary in characteristic $p$, so every supersingular curve has automorphism group $\{\pm1\}$. This is why the [supersingular isogeny graph](../../../ComputerScience/cryptography/public-key/isogeny-and-lattice-foundations/supersingular-isogenies-and-quaternion-orders/supersingular-isogeny-graph.md), whose edges are kernels, can then be drawn undirected.

Let $p$ be a prime with $p\equiv1\pmod{12}$ and $\bar{\mathbb{F}}_p$ an algebraic closure of $\mathbb{F}_p$. Then the elliptic curves over $\bar{\mathbb{F}}_p$ with $j=0$ and with $j=1728$ are not [supersingular](is-supersingular.md), and every supersingular elliptic curve $E$ over $\bar{\mathbb{F}}_p$ has $\operatorname{Aut}(E)=\{\pm1\}$. Consequently, for every prime $\ell\ne p$ and supersingular $E$, $E'$, the number of subgroups of order $\ell$ of $E$ with quotient isomorphic to $E'$ equals the number of subgroups of order $\ell$ of $E'$ with quotient isomorphic to $E$.

## Depends on

- [Supersingular elliptic curves](is-supersingular.md)
- [Automorphism groups of elliptic curves](../automorphism-group-of-an-elliptic-curve.md)
- [Supersingular l-isogeny graphs](../../../ComputerScience/cryptography/public-key/isogeny-and-lattice-foundations/supersingular-isogenies-and-quaternion-orders/supersingular-isogeny-graph.md)

## Proof depends on

- [Every finite subgroup is the kernel of a separable isogeny](../isogenies-of-elliptic-curves/separable-isogeny-with-prescribed-kernel.md)
- [Existence and uniqueness of the dual isogeny](../isogenies-of-elliptic-curves/dual-isogeny.md)
- [Frobenius trace](../point-counts-and-frobenius-traces/frobenius-trace.md)
- [Composition, sum and double-dual rules for dual isogenies](../isogenies-of-elliptic-curves/properties-of-the-dual-isogeny.md), for biduality
- [Hasse bound](../hasse-bound/hasse-bound.md), for the trace estimate

## Expansion

Since $p\ge13$, $\operatorname{Aut}(E)=\{\pm1\}$ unless $j(E)\in\{0,1728\}$, so it suffices that those two curves are ordinary. For $j=1728$ take $y^2=x^3+x$ over $\mathbb{F}_p$ with $p\equiv1\pmod4$: writing $p=a^2+b^2$, its trace of Frobenius is one of $\pm2a,\pm2b$ (Galbraith, Example 9.10.20), which is nonzero and of absolute value at most $2\sqrt p<p$, hence not divisible by $p$. For $j=0$ take $y^2=x^3+1$ with $p\equiv1\pmod3$: writing $p=a^2+ab+b^2$, the trace is one of $\pm(2a+b),\pm(2b+a),\pm(b-a)$ (Galbraith, Exercise 9.10.22), again nonzero and of absolute value at most $2\sqrt p<p$. A curve over $\mathbb{F}_p$ whose trace is prime to $p$ is ordinary (Galbraith, Theorem 9.11.2), and supersingularity depends only on the curve over $\bar{\mathbb{F}}_p$. For the final sentence (Charles, Goren and Lauter, Section 4): for each subgroup $H$ of order $\ell$ of $E$ with $E/H\cong E'$, choose an isogeny $\varphi\colon E\to E'$ with kernel $H$; it is unique up to $\pm1$, so the kernel $H'=\ker\hat\varphi$ of its dual, a subgroup of order $\ell$ of $E'$ with $E'/H'\cong E$, depends only on $H$. Dualizing back recovers $H$, because $\hat{\hat\varphi}=\varphi$ (biduality), so $H\mapsto H'$ is a bijection between the two sets of subgroups. A good expansion adds pages for the trace criterion for supersingularity and for these two point counts.

## Sources

- Denis X. Charles, Eyal Z. Goren, Kristin E. Lauter, "Cryptographic Hash Functions from Expander Graphs", *Journal of Cryptology* 22 (2009) 93–113, [doi:10.1007/s00145-007-9002-x](https://doi.org/10.1007/s00145-007-9002-x), Section 4.
- Anamaria Costache, Brooke Feigon, Kristin Lauter, Maike Massierer, Anna Puskás, "Ramanujan graphs in cryptography", in *Research Directions in Number Theory (Women in Numbers IV)*, Association for Women in Mathematics Series 19, Springer (2019) 1–40, [doi:10.1007/978-3-030-19478-9_1](https://doi.org/10.1007/978-3-030-19478-9_1); numbers from arXiv:1806.05709v2, Section 2, the paragraph after the definition of the supersingular isogeny graph.
- Steven D. Galbraith, *Mathematics of Public Key Cryptography*, Cambridge University Press (2012); extended and corrected version 2.0 of Chapter 9, [author's copy](https://www.math.auckland.ac.nz/~sgal018/crypto-book/ch9.pdf) (numbering of the extended version), Theorem 9.4.4, Example 9.10.20, Exercise 9.10.22 and Theorem 9.11.2.
- Taha Hedayat, Sarah Arpin, Renate Scheidler, "The spine of a supersingular $\ell$-isogeny graph", *Contemporary Mathematics* 840 (2026) 75–101, [doi:10.1090/conm/840/16808](https://doi.org/10.1090/conm/840/16808), Section 2, first paragraph, p. 77 (the criteria for $j=1728$ and $j=0$ to be supersingular, used here for $p>3$).
