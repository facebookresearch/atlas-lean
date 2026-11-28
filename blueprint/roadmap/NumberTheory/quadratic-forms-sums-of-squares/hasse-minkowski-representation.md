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

- the Hasse–Minkowski theorem for representations of $0$ (Serre, Chapter IV, §3.2), with its proof
  by the number of variables $n = 2$, $n = 3$, $n = 4$ and $n \geq 5$;
- the passage between representing $a$ and representing $0$ by $f - a\,x_{n+1}^2$ (Serre,
  Chapter IV, §1.6);
- Hilbert's product formula $\prod_v (a, b)_v = 1$ for nonzero rationals $a, b$ (Serre, Chapter III,
  §2.1), which rests on quadratic reciprocity and the values of $\left(\frac{-1}{p}\right)$
  and $\left(\frac{2}{p}\right)$;
- the approximation theorem: for a finite set $S$ of places of $\mathbb{Q}$, the image of $\mathbb{Q}$
  in $\prod_{v \in S} \mathbb{Q}_v$ is dense (J. S. Milne, *Algebraic Number Theory*, Theorem 7.20, for
  finitely many inequivalent nontrivial absolute values on any field);
- the existence of a rational number with prescribed Hilbert symbols at every place (Serre,
  Chapter III, §2.2): for a finite family $(a_i)_{i \in I}$ of nonzero rationals and signs
  $\varepsilon_{i,v} \in \{\pm 1\}$ for $i \in I$ and every place $v$ of $\mathbb{Q}$, there is
  $x \in \mathbb{Q}^\times$ with $(a_i, x)_v = \varepsilon_{i,v}$ for all $i$ and all $v$ if and only if
  almost all $\varepsilon_{i,v}$ equal $1$, $\prod_v \varepsilon_{i,v} = 1$ for each $i$, and for each
  $v$ there is $x_v \in \mathbb{Q}_v^\times$ with $(a_i, x_v)_v = \varepsilon_{i,v}$ for all $i$. Its
  proof uses the approximation theorem and Dirichlet's theorem on primes in arithmetic progressions
  (Serre, Chapter VI, §4.1; in Mathlib as `Nat.forall_exists_prime_gt_and_eq_mod`);
- the invariants $d$ and $\varepsilon$ of a form over $\mathbb{Q}_p$ (Serre, Chapter IV, §2.1), the
  criteria for representing $0$ in four and more variables (Serre, Chapter IV, §2), and the real case
  by signature (Serre, Chapter IV, §2.4); the ternary case, over $\mathbb{Q}_p$ and over $\mathbb{R}$, is a result of its own.

## Depends on

- [The field of p-adic numbers](../p-adic-numbers/p-adic-numbers.md), for the fields $\mathbb{Q}_p$

## Proof depends on

- [Representation by diagonal ternary forms over $\mathbb{Q}_p$](../p-adic-numbers/hilbert-symbol/diagonal-binary-and-ternary-forms-over-p-and-thr/ternary-criteria.md) and [over $\mathbb{R}$](../p-adic-numbers/hilbert-symbol/diagonal-binary-and-ternary-forms-over-p-and-thr/ternary-criteria-2.md), for the local criteria in three variables
- [Formula for the $p$-adic Hilbert symbol at an odd prime](../p-adic-numbers/hilbert-symbol/odd-formula/eq-formula-of-ne-two.md), for the local Hilbert symbols at odd primes in the product formula and the existence theorem
- [Formula for the $2$-adic Hilbert symbol](../p-adic-numbers/hilbert-symbol/two-formula/eq-formula-two.md), for the local Hilbert symbol at $2$ in the product formula and the existence theorem

The rest of its proof is that of the sources below, as the Expansion describes.

## Sources

- J.-P. Serre, *A Course in Arithmetic*, Graduate Texts in Mathematics 7, Springer, 1973: Chapter IV,
  §3.2 (the Hasse–Minkowski theorem), in §3, pp. 41–45; Chapter IV, §1.6 (represented elements), in §1,
  pp. 27–35, and §2 (quadratic forms over $\mathbb{Q}_p$), pp. 35–41; Chapter III, §2 (global properties of the
  Hilbert symbol: product formula in §2.1, existence theorem in §2.2), pp. 23–27; Chapter VI, §4
  (density and Dirichlet's theorem), pp. 73–77. The preface, p. v, notes
  that Dirichlet's theorem "is used at a critical point in the first part (Chapter III, no. 2.2)".
- J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020),
  <https://www.jmilne.org/math/CourseNotes/ANT.pdf>: Theorem 7.20 (weak approximation), p. 114, in
  the section "The weak approximation theorem", pp. 113–114.
- H. Hasse, "Über die Darstellbarkeit von Zahlen durch quadratische Formen im Körper der rationalen
  Zahlen", *J. Reine Angew. Math.* 152 (1923), 129–148, as cited by J. Robinson (reference [5],
  p. 114).
- J. Robinson, "Definability and decision problems in arithmetic", *J. Symbolic Logic* 14 (1949),
  98–114, <https://doi.org/10.2307/2266510>, p. 107: Lemmas 1 and 2 are special cases of a general
  theorem of Hasse "which gives necessary and sufficient conditions for rational representation of a
  rational number by a given quadratic form in any number of variables".
