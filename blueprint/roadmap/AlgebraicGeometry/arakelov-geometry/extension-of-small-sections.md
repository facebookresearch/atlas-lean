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
- the controlled extension of prescribed products (Zhang, (3.2)–(3.3), pp. 197–198), over one local
  field $K_0$ at a time, archimedean or complete and discretely valued: let $X_0$ be projective over
  $K_0$, $Y_0 \subset X_0$ a closed subvariety defined over $K_0$, $L$ ample with a semiample
  invariant metric, $M$ a coherent sheaf with $M|_{Y_0}$ torsion free and bounded invariant metrics
  as specified there, $\ell'_1, \dots, \ell'_r$ fixed sections of $L|_{Y_0}$ and $m$ a fixed section
  of $M|_{Y_0}$; for every $\varepsilon > 0$ and every multiexponent $\alpha$ with $|\alpha|$ large
  enough, the product $m \prod_i \ell_i'^{\,\alpha_i}$ extends to a section $\ell$ of $L^{\otimes
  |\alpha|} \otimes M$ on $X_0$, over $K_0$, with $\lVert \ell \rVert_{X_0} \le e^{\varepsilon
  |\alpha|} \lVert m \rVert_{Y_0} \prod_i \lVert \ell'_i \rVert_{Y_0}^{\alpha_i}$. The theorem
  concerns these products of fixed sections, not arbitrary sections of $L^{\otimes |\alpha|} \otimes
  M|_{Y_0}$ with the loss measured against their own norms, and it is not a simultaneous lift over
  $\mathbb{Q}$ controlling all places;
- sufficient conditions for a metrization to be semiample (Zhang, Theorem (3.5), p. 200): at the
  archimedean places an extension to an ample bundle with a metric of semipositive curvature, at the
  finite places a model of a positive power with the stated conditions; its conclusion is that $L$
  is semiample metrized, a statement about metrics, not the extension theorem;
- the construction of bases of small sections (Zhang, Theorem (4.2), stated p. 202 and proved pp.
  203–207, with (4.3)–(4.7)): for an irreducible variety over $\mathbb{Q}$, adelic metrized $\bar L$
  and $\bar M$ with $\bar L$ semiample metrized and, on each irreducible subvariety, a strictly
  effective section of some power of $\bar L$, for all sufficiently large $n$ the lattice of
  sections of $L^{\otimes n} \otimes M$ of norm at most $1$ at every finite place has a
  $\mathbb{Z}$-basis of sections of norm less than $1$ at the infinite place, through lattice
  filtrations and successive minima (p. 203); the threshold depends on the fixed twist $M$. Strict
  smallness is asked only at infinity: a rational number of norm less than $1$ at every prime and at
  most $1$ at infinity is $0$.

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
  <https://web.math.princeton.edu/~shouwu/publications/plav.pdf>: (2.2)–(2.4), pp. 193–194; (3.2)
  and Theorem (3.3), pp. 197–198; Theorem (3.5), p. 200; Theorem (4.2), p. 202, with its proof
  (4.3)–(4.7), pp. 203–207.
