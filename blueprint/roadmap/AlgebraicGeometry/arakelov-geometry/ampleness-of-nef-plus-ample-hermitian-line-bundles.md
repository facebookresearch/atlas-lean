# Ampleness of nef plus ample hermitian line bundles

This node is still to be broken down: the statement is precise, but no source proves it in this
generality.

Let $X$ be a projective arithmetic variety in Moriwaki's sense, an integral scheme projective and
flat over $\operatorname{Spec} \mathbb{Z}$ whose generic fibre need not be smooth, and let $\bar L$
and $\bar A$ be $C^\infty$-hermitian line bundles on $X$, with $\bar L$ nef and $\bar A$ ample in
Moriwaki's sense (see
[positivity of hermitian line bundles](positivity-of-hermitian-line-bundles.md)). Then $b \bar L + a
\bar A$ is ample for all positive integers $a$ and $b$; equivalently, $\bar L + \varepsilon \bar A$
is an ample hermitian $\mathbb{Q}$-line bundle for every rational $\varepsilon > 0$.

Moriwaki uses this without proof in *Continuity of volumes*: in Claim 5.5.1 of the proof of his
Corollary 5.5, for $\bar L + \varepsilon \bar A$ and for $p \bar L - (k \bar L - \bar A) = (p - k)
\bar L + \bar A$ with $p \ge k$, and in the proof of his Theorem 5.6, for $\bar L + \varepsilon \bar
A$ and $\bar M + \varepsilon \bar A$ with $\bar L$ and $\bar M$ nef (pp. 38–39). The case $a = 1$,
$b = p - k$ is the second form, and $p = k$ is $\bar A$ itself.
[Zhang's arithmetic ampleness theorem](arithmetic-ampleness-theorem.md) does not give it alone: it
starts from a bundle that is already ample in Zhang's sense and produces bases of small sections.

A good expansion has pages for:

- the ampleness of $bL + aA$ on $X$: on every closed fibre of $X$ over $\operatorname{Spec}
  \mathbb{Z}$, a projective scheme over a field, $L$ is nef and $A$ is ample, so $bL + aA$ is ample
  there by the Nakai–Moishezon criterion and Kleiman's nonnegativity of intersection numbers of nef
  line bundles; and a line bundle on a scheme proper over $\operatorname{Spec} \mathbb{Z}$ that is
  ample on every closed fibre is ample, by Grothendieck's criterion (EGA III, Théorème (4.7.1));
- the positivity of the first Chern form $c_1(b \bar L + a \bar A) = b\, c_1(\bar L) + a\, c_1(\bar
  A)$, semipositive plus positive;
- horizontal positivity, $(\hat c_1(b \bar L + a \bar A)|_Y)^{\dim Y} > 0$ for every horizontal
  irreducible closed subvariety $Y$, from the nonnegativity of mixed arithmetic intersection numbers
  of nef hermitian line bundles and the strict positivity after an ample perturbation (Moriwaki,
  *Arithmetic height functions over finitely generated fields*, Proposition 2.3 (1) and Lemma 2.4,
  pp. 7–9);
- the generation of the multiples of $bL + aA$ by sections of sup norm less than $1$: Zhang's
  Corollary (5.7) (2), which gives bases of small sections from a positive uniform lower bound for
  the heights of points under generic ampleness and relative semiampleness; Zhang's (4.8) when the
  generic fibre is regular; and Moriwaki's Theorem 4.2 in *Free basis consisting of strictly small
  sections* for generically smooth $X$. No source has been identified for a singular generic fibre.

## Depends on

- [Positivity of hermitian line bundles](positivity-of-hermitian-line-bundles.md), for Moriwaki's
  nef and ample hermitian line bundles and for hermitian $\mathbb{Q}$-line bundles
- [Arithmetic varieties and hermitian vector bundles](arithmetic-variety.md)

## Proof depends on

- [Standard results of coherent cohomology on projective varieties](../birational-geometry/standard-results-of-coherent-cohomology.md),
  for the Nakai–Moishezon criterion on the closed fibres
- [Arithmetic degree and arithmetic intersection numbers](arithmetic-intersection-numbers.md), for
  the arithmetic intersection numbers of the horizontal positivity
- [Zhang's arithmetic ampleness theorem](arithmetic-ampleness-theorem.md), for the bases of small
  sections when the generic fibre is smooth

The other steps of its proof are not pages here: Grothendieck's fibrewise criterion for ampleness
(EGA III, Théorème (4.7.1)); Kleiman's nonnegativity of intersection numbers of nef line bundles on
the closed fibres, which the page on intersection numbers of nef line bundles states but which
depends, through the coordinate lattices of arithmetic volumes, on the consumers of this node;
Moriwaki's nonnegativity and perturbation results for mixed arithmetic intersection numbers; and the
generation by small sections when the generic fibre is singular, for which no source has been
identified.

## Sources

- A. Moriwaki, "Continuity of volumes on arithmetic varieties", J. Algebraic Geom. 18 (2009),
  407–457, arXiv:math/0612269 (version 2), <https://arxiv.org/abs/math/0612269v2>: the proofs of
  Corollary 5.5 (Claim 5.5.1) and Theorem 5.6, pp. 38–39.
- A. Moriwaki, "Arithmetic height functions over finitely generated fields", arXiv:math/9809016
  (version 2), <https://arxiv.org/abs/math/9809016v2>: Proposition 2.3 (1) and Lemma 2.4 with its
  proof, pp. 7–9.
- S.-W. Zhang, "Positive line bundles on arithmetic varieties", J. Amer. Math. Soc. 8 (1995),
  187–221, author's scan of the printed edition
  <https://web.math.princeton.edu/~shouwu/publications/plav.pdf>: (4.8), p. 207, and Corollary (5.7)
  (2), p. 211.
- A. Moriwaki, "Free basis consisting of strictly small sections", arXiv:0903.3778 (version 2),
  <https://arxiv.org/abs/0903.3778v2>: Theorem 4.2, p. 14.
- A. Grothendieck, "Éléments de géométrie algébrique III. Étude cohomologique des faisceaux
  cohérents, première partie", Publ. Math. IHÉS 11 (1961), 5–167,
  <https://www.numdam.org/item/PMIHES_1961__11__5_0/>: Théorème (4.7.1), p. 145.
