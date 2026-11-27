# Collisions and preimages of the endpoint walk give isogenies between supersingular curves

Two digit strings with the same endpoint under the Charles–Goren–Lauter walk give two isogenies of degree $\ell^n$ with different kernels between two supersingular curves, and an endomorphism of the start curve of degree $\ell^{2n}$ other than $\pm[\ell^n]$. A string mapping to a given $j$-invariant gives an isogeny of degree $\ell^n$ to a curve with that $j$-invariant.

Let $h$ be the [Charles–Goren–Lauter walk with endpoint output](cgl-endpoint-walk-hash.md), with primes $p\equiv1\pmod{12}$ and $\ell\ne p$, length $n$, start curve $E_0=E_{j_0}$ and injective labelling as there. All isogenies are over $\bar{\mathbb{F}}_p$.

1. **Collisions.** Let $d\ne d'$ in $\{0,\dots,\ell-1\}^n$ with $h(d)=h(d')=v$, and let $f,f'\colon E_0\to E_v$ be the composites $\varphi'_n\circ\cdots\circ\varphi'_1$ of the two walks, which end on the same fixed curve $E_v$. Then $f$ and $f'$ are cyclic isogenies of degree $\ell^n$ with $\ker f\ne\ker f'$, and

$$
\alpha=\hat{f}'\circ f\in\operatorname{End}(E_0),\qquad \deg\alpha=\ell^{2n},\qquad \alpha\ne\pm[\ell^n] .
$$

   So a collision gives, for $E_1=E_0$ and $E_2=E_v$, a solution of Charles, Goren and Lauter's Problem 1 (two isogenies $E_1\to E_2$ of degree $\ell^n$ with different kernels) and of their Problem 2 (an endomorphism of $E_1$ of degree $\ell^{2n}$ that is not an automorphism composed with $[\ell^n]$), as geometric maps.
2. **Preimages.** If $h(d)=y$, the walk of $d$ is a chain of $n$ isogenies of degree $\ell$ from $E_0$ to $E_y$, without backtracking, whose composite is an isogeny $E_0\to E_y$ of degree $\ell^n$ over $\bar{\mathbb{F}}_p$; composing with an isomorphism over $\bar{\mathbb{F}}_p$ gives one to any curve $E'$ with $j(E')=y$, the form of their Problem 3. Not every supersingular $j$-invariant need be an output for a given $n$.

The maps are over $\bar{\mathbb{F}}_p$. For a model $E'$ over $\mathbb{F}_{p^2}$ with $j(E')=y$ the statement gives no isogeny defined over $\mathbb{F}_{p^2}$: for $p\equiv1\pmod{12}$ a supersingular curve over $\mathbb{F}_{p^2}$ has trace of Frobenius $\pm2p$ (Waterhouse's theorem), its quadratic twist has the same $j$-invariant and the opposite trace, so the two have different numbers of $\mathbb{F}_{p^2}$-points, and an $\mathbb{F}_{p^2}$-rational isogeny preserves that number; at most one of them is $\mathbb{F}_{p^2}$-isogenous to a given curve.

These are implications from a collision or preimage of $h$, a fixed-length map with endpoint output, to solutions of the isogeny problems; they assert nothing about how hard those problems are, and they do not cover the compressed output of the paper, inputs of different lengths, or a non-injective encoding of inputs.

## Depends on

- [The Charles–Goren–Lauter walk with endpoint output](cgl-endpoint-walk-hash.md)
- [Supersingular elliptic curves and isogenies](supersingular-curves.md)
- [Existence and uniqueness of the dual isogeny](../../../../../AlgebraicGeometry/elliptic-curves/isogenies-of-elliptic-curves/dual-isogeny.md)

## Proof depends on

- [Two different equal-length paths between supersingular curves give a non-scalar endomorphism](../../../../../AlgebraicGeometry/elliptic-curves/isogeny-chains-and-supersingular-graphs/distinct-equal-length-paths-give-a-non-scalar-endomorphism.md)
- [Cyclic prime-power isogenies correspond to chains without backtracking](../../../../../AlgebraicGeometry/elliptic-curves/isogeny-chains-and-supersingular-graphs/cyclic-isogenies-correspond-to-non-backtracking-chains.md)
- [A chain without backtracking composes to a cyclic isogeny](../../../../../AlgebraicGeometry/elliptic-curves/isogeny-chains-and-supersingular-graphs/non-backtracking-chain-composes-to-cyclic-isogeny.md)
- [Degrees of isogenies multiply under composition](../../../../../AlgebraicGeometry/elliptic-curves/isogenies-of-elliptic-curves/degree-is-multiplicative.md)
- [Supersingular curves have only the automorphisms plus or minus one when p is 1 mod 12](../../../../../AlgebraicGeometry/elliptic-curves/supersingular-elliptic-curves/supersingular-automorphisms-when-p-is-one-mod-twelve.md)
- [Tate's isogeny theorem for elliptic curves over finite fields](../../../../../AlgebraicGeometry/elliptic-curves/isogenies-of-elliptic-curves/tate-isogeny-theorem.md)
- [Waterhouse's theorem on Frobenius traces](../../../../../AlgebraicGeometry/elliptic-curves/point-counts-and-frobenius-traces/exists-is-elliptic-frobenius-trace-eq-if.md)

## Expansion

Both walks run on the same fixed curves $E_j$ and start from the same curve $E_0$ with the identity, so they can be compared step by step. Let $i$ be the first index with $d_i\ne d'_i$. For $i'<i$ the two walks use the same label at the same vertex with the same excluded subgroup, hence the same kernel $H_{i'}$ and the same next vertex; their maps $\varphi'_{i'}$ then have the same kernel and the same target curve, so they differ by an automorphism of the target, that is by $\pm1$. So the prefix composites $g,g'\colon E_0\to E_{v_{i-1}}$ satisfy $g'=\pm g$, the excluded subgroups at step $i$ agree because $\pm1$ fixes subgroups, and the injective labelling gives $H_i\ne H'_i$. The kernels of the length-$i$ prefixes are $g^{-1}(H_i)\ne g^{-1}(H'_i)$, as $g$ is surjective. Both walks are chains without backtracking, so their composites are cyclic and their partial kernels are the subgroups of the composite kernels of order $\ell^i$; hence $\ker f\ne\ker f'$ and the chains are inequivalent. The page on equal-length paths then gives the degree of $\alpha$ and $\alpha\ne\pm[\ell^n]$. Comparing vertex sequences would not suffice: two walks can visit the same vertices along different edges, and $f$, $-f$ are different maps with the same kernel. The preimage statement is the definition of the walk.

Charles, Goren and Lauter prove their Theorems 1 and 2 by treating a collision as two paths of the same length between the same two vertices and a preimage as a path; this page states the corresponding implications for the endpoint walk defined above. The twist remark combines Waterhouse's theorem (for $q=p^2$ and $p\equiv1\pmod{12}$ a trace divisible by $p$ is $\pm2p$), Galbraith's point count $q+1+t$ of the quadratic twist (Section 9.5) and the easy direction of Tate's isogeny theorem (an $\mathbb{F}_{p^2}$-isogeny preserves the number of points). The automorphism statement uses $\operatorname{Aut}(E_0)=\{\pm1\}$ for $p\equiv1\pmod{12}$.

## Sources

- Denis X. Charles, Eyal Z. Goren, Kristin E. Lauter, "Cryptographic Hash Functions from Expander Graphs", *Journal of Cryptology* 22 (2009) 93–113, [doi:10.1007/s00145-007-9002-x](https://doi.org/10.1007/s00145-007-9002-x), Proposition 1, Problems 1–3, Theorems 1 and 2 with their proofs.
- Anamaria Costache, Brooke Feigon, Kristin Lauter, Maike Massierer, Anna Puskás, "Ramanujan graphs in cryptography", in *Research Directions in Number Theory (Women in Numbers IV)*, Association for Women in Mathematics Series 19, Springer (2019) 1–40, [doi:10.1007/978-3-030-19478-9_1](https://doi.org/10.1007/978-3-030-19478-9_1); numbers from arXiv:1806.05709v2, Lemmas 4.2 and 4.4, Corollary 4.5.
- Luca De Feo, "Mathematics of Isogeny Based Cryptography", lecture notes, arXiv:1711.04062v1 (2017), Section 13, Problems 4 and 5.
- Steven D. Galbraith, *Mathematics of Public Key Cryptography*, Cambridge University Press (2012); extended and corrected version 2.0 of Chapter 9, [author's copy](https://www.math.auckland.ac.nz/~sgal018/crypto-book/ch9.pdf) (numbering of the extended version), Section 9.5, Theorem 9.7.4 and Theorem 9.10.12.
