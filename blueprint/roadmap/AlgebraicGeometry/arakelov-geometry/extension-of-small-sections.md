# Extension of small sections and bases of small sections

This node is still to be broken down. It covers the steps of Zhang's proof of his
[arithmetic ampleness theorem](arithmetic-ampleness-theorem.md) other than the arithmetic
Hilbert–Samuel theorem: the extension of small sections from a subvariety with control of their
norms, the semiampleness of metrizations, and the passage from strictly small sections on every
horizontal subvariety to bases of small sections, through filtrations of lattices and their
successive minima.

A good expansion has pages for:

- the $L^2$ estimates for $\bar\partial$ with weights on the complex points (Zhang, (2.2)–(2.4), pp.
  193–194, after Hörmander; the
  [L² estimates for the ∂̄ operator](../birational-geometry/l2-estimates-for-the-dbar-operator.md)
  node contains the underlying existence theorem), one archimedean ingredient of the following;
- the controlled extension of prescribed products (Zhang, Theorem (3.3), p. 198): let $L$ be ample
  with a semiample invariant metric, $M$ a coherent sheaf with bounded metrics as specified there,
  $Y \subset X$ a closed subvariety, $\ell'_1, \dots, \ell'_r$ fixed sections of $L|_Y$ and $m$ a
  fixed section of $M|_Y$; for every $\varepsilon > 0$ and every multiexponent $\alpha$ with
  $|\alpha|$ large enough, the product $m \prod_i \ell_i'^{\,\alpha_i}$ extends to a section $\ell$
  of $L^{\otimes |\alpha|} \otimes M$ on $X$ with $\lVert \ell \rVert_X \le e^{\varepsilon |\alpha|}
  \lVert m \rVert_Y \prod_i \lVert \ell'_i \rVert_Y^{\alpha_i}$, at the archimedean and at the
  finite places. The theorem concerns these products of fixed sections, not arbitrary sections of
  $L^{\otimes |\alpha|} \otimes M|_Y$ with the loss measured against their own norms;
- sufficient conditions for a metrization to be semiample (Zhang, Theorem (3.5), p. 200): at the
  archimedean places an extension to an ample bundle with a metric of semipositive curvature, at the
  finite places a model of a positive power with the stated conditions; its conclusion is that $L$
  is semiample metrized, a statement about metrics, not the extension theorem;
- the construction of bases of small sections (Zhang, Theorem (4.2), stated p. 202 and proved pp.
  203–207, with (4.3)–(4.7)): for an irreducible variety over $\mathbb{Q}$, adelic metrized $\bar L$
  and $\bar M$ with $\bar L$ semiample metrized and, on each irreducible subvariety, a strictly
  effective section of some power of $\bar L$, the sections of $L^{\otimes n} \otimes M$ have bases
  of strictly small sections for all sufficiently large $n$, through lattice filtrations and
  successive minima; the threshold depends on the fixed twist $M$.

Zhang's Corollary (4.8), the application of (4.2) with (1.9) and (3.5) to arithmetically ample line
bundles, belongs to the ampleness theorem, not to this node.

## Depends on

- [Positivity of hermitian line bundles](positivity-of-hermitian-line-bundles.md)

## Proof depends on

- [L² estimates for the ∂̄ operator](../birational-geometry/l2-estimates-for-the-dbar-operator.md), for
  Zhang's (2.2)–(2.4)
- [Small elements of normed lattices](small-elements-of-normed-lattices.md), for the successive minima
  in Zhang's (4.3)–(4.7)

## Sources

- S.-W. Zhang, "Positive line bundles on arithmetic varieties", J. Amer. Math. Soc. 8 (1995),
  187–221, author's scan of the printed edition
  <https://web.math.princeton.edu/~shouwu/publications/plav.pdf>: (2.2)–(2.4), pp. 193–194; Theorem
  (3.3), p. 198; Theorem (3.5), p. 200; Theorem (4.2), p. 202, with its proof (4.3)–(4.7), pp.
  203–207.
