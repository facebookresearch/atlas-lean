# No loops or double edges in the supersingular 2-isogeny graph when p is 1 mod 840

If $p\equiv 1\pmod{840}$, no supersingular elliptic curve in characteristic $p$ has an endomorphism of degree $2$, and two different subgroups of order $2$ of such a curve never have isomorphic quotients. So the supersingular $2$-isogeny graph has no loops and no multiple edges.

Let $p$ be a prime with $p\equiv 1\pmod{840}$, where $840=2^3\cdot3\cdot5\cdot7$, and let $E$ be a [supersingular](../supersingular-elliptic-curves/is-supersingular.md) elliptic curve over an algebraic closure $\bar{\mathbb{F}}_p$ of $\mathbb{F}_p$. Then:

1. $E$ has no endomorphism of degree $2$; equivalently, $E/H\not\cong E$ for every subgroup $H$ of order $2$;
2. if $H\ne H'$ are subgroups of order $2$ of $E(\bar{\mathbb{F}}_p)$, then $E/H\not\cong E/H'$.

Since $p\equiv 1\pmod{12}$, every supersingular curve also has automorphism group $\{\pm1\}$, so the [supersingular $2$-isogeny graph](../../../ComputerScience/cryptography/public-key/isogeny-and-lattice-foundations/supersingular-isogenies-and-quaternion-orders/supersingular-isogeny-graph.md), whose edges from a curve are its three subgroups of order $2$ (kernels, not neighbouring $j$-invariants), is undirected, $3$-regular and simple.

## Depends on

- [Supersingular elliptic curves](../supersingular-elliptic-curves/is-supersingular.md)
- [Every finite subgroup is the kernel of a separable isogeny](../isogenies-of-elliptic-curves/separable-isogeny-with-prescribed-kernel.md)
- [Supersingular l-isogeny graphs](../../../ComputerScience/cryptography/public-key/isogeny-and-lattice-foundations/supersingular-isogenies-and-quaternion-orders/supersingular-isogeny-graph.md)

## Proof depends on

- [Two different equal-length paths without backtracking between supersingular curves give a non-scalar endomorphism](distinct-equal-length-paths-give-a-non-scalar-endomorphism.md)
- [Counting subgroups of prime-power order in the torsion of an elliptic curve](number-of-cyclic-subgroups-of-prime-power-torsion.md)
- [Supersingularity is an isogeny invariant](../isogenies-of-elliptic-curves/supersingularity-is-an-isogeny-invariant.md)
- [Multiplication by m has degree m squared](../isogenies-of-elliptic-curves/degree-of-multiplication-by-m.md)
- [Supersingular curves have only the automorphisms plus or minus one when p is 1 mod 12](../supersingular-elliptic-curves/supersingular-automorphisms-when-p-is-one-mod-twelve.md)
- [The Deuring correspondence between supersingular curves and maximal orders](../../../ComputerScience/cryptography/public-key/isogeny-and-lattice-foundations/supersingular-isogenies-and-quaternion-orders/deuring-correspondence.md)
- [The quaternion algebra ramified at p and infinity and its maximal orders](../../../ComputerScience/cryptography/public-key/isogeny-and-lattice-foundations/supersingular-isogenies-and-quaternion-orders/quaternion-algebra-bp.md)

## Expansion

A non-scalar endomorphism $\alpha$ of degree $d$ satisfies $\alpha^2-t\alpha+d=0$ with $t\in\mathbb{Z}$ and $t^2<4d$, so $\mathbb{Q}(\alpha)$ is an imaginary quadratic field contained in $\operatorname{End}(E)\otimes\mathbb{Q}$, which for supersingular $E$ is the quaternion algebra over $\mathbb{Q}$ ramified exactly at $p$ and $\infty$. A quadratic field embeds in that algebra only if $p$ does not split in it. Item 1: an endomorphism of degree $2$ is non-scalar, since $\deg[m]=m^2$ is never $2$; $t\in\{0,\pm1,\pm2\}$ and the discriminants $t^2-8$ give the fields $\mathbb{Q}(\sqrt{-2})$, $\mathbb{Q}(\sqrt{-7})$, $\mathbb{Q}(\sqrt{-1})$. Item 2: $E'$ is supersingular, being isogenous to $E$, and two $2$-isogenies $E\to E'$ with different kernels are two inequivalent chains of length $1$, so by the page on equal-length paths (with $n=1$, using $p\equiv1\pmod{12}$) they give a non-scalar $\alpha$ of degree $4$, so $t\in\{0,\pm1,\pm2,\pm3\}$ and the fields are $\mathbb{Q}(\sqrt{-1})$, $\mathbb{Q}(\sqrt{-15})$, $\mathbb{Q}(\sqrt{-3})$, $\mathbb{Q}(\sqrt{-7})$. The congruence $p\equiv1$ modulo $8$, $3$, $5$ and $7$ makes $p$ split in all of these, by quadratic reciprocity, a contradiction. A good expansion adds pages for the characteristic polynomial $\alpha^2-t\alpha+\deg\alpha$ of an endomorphism, and for the criterion that a quadratic field embeds in a quaternion algebra over $\mathbb{Q}$ exactly when no ramified place splits in it.

Charles, Goren and Lauter give this example for $\ell=2$ (cycles of length $2$, plus loops). Costache, Feigon, Lauter, Massierer and Puskás state the weaker claim that $p\equiv1\pmod{420}$ excludes double edges, which drops the loop condition at $\mathbb{Q}(\sqrt{-2})$.

## Sources

- Denis X. Charles, Eyal Z. Goren, Kristin E. Lauter, "Cryptographic Hash Functions from Expander Graphs", *Journal of Cryptology* 22 (2009) 93–113, [doi:10.1007/s00145-007-9002-x](https://doi.org/10.1007/s00145-007-9002-x), Section 5.3.4.
- Anamaria Costache, Brooke Feigon, Kristin Lauter, Maike Massierer, Anna Puskás, "Ramanujan graphs in cryptography", in *Research Directions in Number Theory (Women in Numbers IV)*, Association for Women in Mathematics Series 19, Springer (2019) 1–40, [doi:10.1007/978-3-030-19478-9_1](https://doi.org/10.1007/978-3-030-19478-9_1); numbers from arXiv:1806.05709v2, Remark 2.4.
- John Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer (2021), [doi:10.1007/978-3-030-56694-4](https://doi.org/10.1007/978-3-030-56694-4); numbers from the author's corrected edition v.1.0.7u, [author's copy](https://jvoight.github.io/quat-book.pdf), Proposition 14.6.7 and Theorem 42.1.9.
- Steven D. Galbraith, *Mathematics of Public Key Cryptography*, Cambridge University Press (2012); extended and corrected version 2.0 of Chapter 9, [author's copy](https://www.math.auckland.ac.nz/~sgal018/crypto-book/ch9.pdf) (numbering of the extended version), Theorem 9.9.3.
