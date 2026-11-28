# Hasse–Minkowski theorem for representations of rationals

Let $f(x) = \sum_{i,j=1}^n a_{ij} x_i x_j$ be a nondegenerate quadratic form with rational
coefficients ($a_{ij} = a_{ji} \in \mathbb{Q}$, $\det(a_{ij}) \neq 0$, $n \geq 1$) and let $a$ be a
nonzero rational number. Then $f(x) = a$ has a solution $x \in \mathbb{Q}^n$ if and only if it has a
solution $x \in \mathbb{R}^n$ and a solution $x \in \mathbb{Q}_p^n$ for every prime $p$.

This node is still to be broken down. It covers the local–global principle for quadratic forms over
$\mathbb{Q}$ in the form stated above, which follows from the Hasse–Minkowski theorem for
representations of $0$ (a nondegenerate form represents $0$ nontrivially over $\mathbb{Q}$ if and
only if it does over $\mathbb{R}$ and over every $\mathbb{Q}_p$) applied to $f(x) - a\,x_{n+1}^2$.
J. Robinson describes the 1923 paper of Hasse that she cites for her Lemmas 1 and 2 as giving
necessary and sufficient conditions for the rational representation of a rational number by a given
quadratic form in any number of variables.

## Expansion

A good expansion states and links:

- the reduction to diagonal forms: every quadratic form over $\mathbb{Q}$ is equivalent, by an
  invertible linear change of variables, to a diagonal form $a_1 x_1^2 + \dots + a_n x_n^2$
  (A. V. Sutherland, Lecture 9, Theorem 9.5);
- the case $n \geq 5$ of the Hasse–Minkowski theorem for representations of $0$ by nondegenerate
  diagonal forms in $n$ variables (Sutherland, Lecture 11, Theorem 11.12, case $n \geq 5$, p. 5),
  by induction on $n$ from the
  [case $n = 4$](exists-quaternary-eq-zero-of-forall-loca.md). Its proof uses
  [the density of $\mathbb{Q}$ in a finite product of its completions](../local-global-facts-about-the-rationals/dense-range-embedding-pi.md),
  [the isotropy of unit diagonal forms in at least three variables over $\mathbb{Q}_p$ for odd $p$](../../p-adic-numbers/hilbert-symbol/diagonal-unit-isotropic.md),
  which leaves finitely many places where $a_3 x_3^2 + \dots + a_n x_n^2$ has no nonzero zero
  (Corollary 11.2),
  [the fact that a nondegenerate form with a nonzero zero represents every element](../../../LinearAlgebra/bilinear-and-quadratic-forms/isotropic-quadratic-forms-over-a-field/exists-apply-eq-of-isotropic.md),
  and the openness of each square class $t\,\mathbb{Q}_v^{\times 2}$ in $\mathbb{Q}_v^\times$
  (p. 5, footnote 1);
- the passage between representing $a$ and representing $0$ by $f - a\,x_{n+1}^2$ (Serre,
  Chapter IV, §1.6). A zero with $x_{n+1} \neq 0$ gives a representation of $a$ after scaling; a
  zero with $x_{n+1} = 0$ is a nonzero zero of $f$, and then $f$ represents $a$ by
  [the fact that a nondegenerate form with a nonzero zero represents every element](../../../LinearAlgebra/bilinear-and-quadratic-forms/isotropic-quadratic-forms-over-a-field/exists-apply-eq-of-isotropic.md).

The cases $n \leq 4$ of the theorem for representations of $0$ by nondegenerate diagonal forms
follow Sutherland's proof, pp. 4–5: $n = 1$ is trivial; $n = 2$ follows from
[a rational number that is a square at every place is a square](../local-global-facts-about-the-rationals/is-square-of-is-square-real-of-forall-is.md)
and [the criterion for a diagonal binary form to have a nonzero zero](../../../LinearAlgebra/bilinear-and-quadratic-forms/isotropic-quadratic-forms-over-a-field/exists-ne-zero-mul-sq-add-mul-sq-eq-zero.md);
$n = 3$ and $n = 4$ are the [ternary case](exists-ternary-eq-zero-of-forall-local.md) and the
[quaternary case](exists-quaternary-eq-zero-of-forall-loca.md). In that proof the ternary local
criterion, Hilbert's product formula and Dirichlet's theorem on primes in arithmetic progressions
enter only the case $n = 4$.

## Depends on

- [The field of p-adic numbers](../../p-adic-numbers/p-adic-numbers.md), for the fields $\mathbb{Q}_p$

## Proof depends on

- [Hasse–Minkowski theorem for diagonal ternary forms over $\mathbb{Q}$](exists-ternary-eq-zero-of-forall-local.md) and [for diagonal quaternary forms](exists-quaternary-eq-zero-of-forall-loca.md), for the cases $n = 3$ and $n = 4$ of the theorem for representations of $0$, and the second as the base of the induction for $n \geq 5$
- [A rational number that is a square at every place is a square](../local-global-facts-about-the-rationals/is-square-of-is-square-real-of-forall-is.md) and [When a diagonal binary form has a nonzero zero](../../../LinearAlgebra/bilinear-and-quadratic-forms/isotropic-quadratic-forms-over-a-field/exists-ne-zero-mul-sq-add-mul-sq-eq-zero.md), for the case $n = 2$
- [The rationals are dense in a finite product of their completions](../local-global-facts-about-the-rationals/dense-range-embedding-pi.md), for the case $n \geq 5$
- [Unit diagonal forms in at least three variables over $\mathbb{Q}_p$ are isotropic for odd $p$](../../p-adic-numbers/hilbert-symbol/diagonal-unit-isotropic.md), for the case $n \geq 5$
- [A nondegenerate quadratic form with a nonzero zero represents every element](../../../LinearAlgebra/bilinear-and-quadratic-forms/isotropic-quadratic-forms-over-a-field/exists-apply-eq-of-isotropic.md), for the case $n \geq 5$ and the passage between representing $a$ and representing $0$

The rest of its proof is that of the sources below, as the Expansion describes.

## Sources

- A. V. Sutherland, *18.782 Introduction to Arithmetic Geometry*, MIT, Fall 2013, lecture notes:
  Lecture 9, Theorem 9.5 (diagonalization), p. 2, and Theorem 9.9, p. 3,
  <https://math.mit.edu/classes/18.782/2013fa/LectureNotes9.pdf>; Lecture 11, Theorem 11.12 and its
  proof, pp. 4–5, with Corollary 11.2, p. 1, and Theorem 11.7, p. 2,
  <https://math.mit.edu/classes/18.782/2013fa/LectureNotes11.pdf>.
- J.-P. Serre, *A Course in Arithmetic*, Graduate Texts in Mathematics 7, Springer, 1973: Chapter IV,
  §3.2 (the Hasse–Minkowski theorem), in §3, pp. 41–45; Chapter IV, §1.6 (represented elements), in §1,
  pp. 27–35.
- H. Hasse, "Über die Darstellbarkeit von Zahlen durch quadratische Formen im Körper der rationalen
  Zahlen", *J. Reine Angew. Math.* 152 (1923), 129–148, as cited by J. Robinson (reference [5],
  p. 114).
- J. Robinson, "Definability and decision problems in arithmetic", *J. Symbolic Logic* 14 (1949),
  98–114, <https://doi.org/10.2307/2266510>, p. 107: Lemmas 1 and 2 are special cases of a general
  theorem of Hasse "which gives necessary and sufficient conditions for rational representation of a
  rational number by a given quadratic form in any number of variables".
