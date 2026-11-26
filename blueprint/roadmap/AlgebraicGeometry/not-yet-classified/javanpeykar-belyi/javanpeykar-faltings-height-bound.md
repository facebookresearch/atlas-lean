# Javanpeykar's bound for the Faltings height of a Belyi curve

Let $X$ be a smooth
projective connected curve of genus $g \ge 1$ over $\overline{\mathbb{Q}}$, and let
$h_{\mathrm{Fal}}(X)$ be its Faltings height, the stable Faltings height of its Jacobian in
Faltings' normalization. Then

$$-g \log(2\pi) \le h_{\mathrm{Fal}}(X) \le 13 \cdot 10^6 \, g \, \deg_B(X)^5,$$

where $\deg_B(X)$ is the Belyi degree of $X$.

Every such curve is defined over a number field, so the statement takes a number field $K$ and a
curve $C$ over $K$ (proper, smooth of relative dimension $1$, geometrically irreducible) of genus
$g \ge 1$, with $X = C_{\bar K}$ over the algebraic closure $\bar K$ of $K$, an algebraic
closure of $\mathbb{Q}$. Then $h_{\mathrm{Fal}}(X) = h_F(J(C))$, the genus of $X$ is that of
$C$, and the Belyi degree is computed over $\bar K$. The hypothesis that $X$ has a Belyi map is
Belyi's theorem; it makes $\deg_B(X)$ the minimum of the degrees of Belyi maps. The theorem also
bounds three further Arakelov invariants of $X$ (the self-intersection of the dualizing sheaf,
the discriminant and Faltings' delta invariant); those bounds are not part of this statement.

The Jacobian $J(C)$ of $C$ enters through its underlying $K$-scheme: the statement takes any
abelian variety $J$ over $K$ whose underlying $K$-scheme is isomorphic to $J(C)$, and bounds
$h_F(J)$. This does not depend on the choice of $J$: a morphism of abelian varieties is a
homomorphism followed by a translation (J. S. Milne, *Abelian Varieties*, course notes, version
2.00 (2008), Chapter I, Corollary 1.2, p. 9, <https://www.jmilne.org/math/CourseNotes/AV.pdf>),
so an isomorphism of $K$-schemes between two abelian varieties, followed by the translation that
takes the image of the origin back to the origin, is an isomorphism of abelian varieties. Hence
the abelian variety structures on one $K$-scheme give isomorphic abelian varieties, every such
$J$ is isomorphic to $J(C)$ with its group law, and $h_F(J) = h_F(J(C)) = h_{\mathrm{Fal}}(X)$.

## Sources

- A. Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra Number Theory 8 (2014), 89–140, Theorem 1.1.1, p. 90, with $h_{\mathrm{Fal}}$ defined in §2.3, where it is identified with the stable Faltings height of the Jacobian, and its normalization compared with that of Gaudron and Rémond in Lemma 2.4.4, <https://doi.org/10.2140/ant.2014.8.89> (arXiv:1403.6404v1).
