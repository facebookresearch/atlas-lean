# Presburger arithmetic with a rounded Hardy field function of polynomial growth is undecidable

Adding to the integers with order and addition the nearest-integer rounding of a Hardy field function that grows polynomially but is not asymptotically linear or slower than every positive power gives an undecidable theory.

**Theorem (Brown and Konieczny).** Call two continuous real functions equivalent if they agree on some interval $[x_0, \infty)$; the equivalence classes (germs) form a ring, a *Hardy field* is a subfield of this ring closed under differentiation, and a *Hardy field function* is a function whose germ lies in some Hardy field, extended by $0$ outside its domain $[x_0, \infty)$. For a real function $f$ let $\lfloor f\rceil(n) = \lceil f(n) - 1/2\rceil$, the nearest integer to $f(n)$, rounding half down, as the source defines the function of its theorems (Sections 1.2 and 1.5 of arXiv:2508.19206v1; Sections 1.1 and 1.4 of the STACS version). Let $f$ be a Hardy field function. Then the first-order theory $\mathrm{Th}(\mathbb Z; <, +, \lfloor f\rceil)$ is undecidable in each of the following cases:

1. $\lim_{x \to \infty} f(x)/x = \infty$ and $\lim_{x \to \infty} f(x)/x^d = 0$ for some integer $d \ge 2$ (Theorem A of the source);
2. $\lim_{x \to \infty} f(x)/x^{\varepsilon} = \infty$ for some $\varepsilon > 0$ and $\lim_{x \to \infty} f(x)/x = 0$ (Theorem B).

Hardy field functions include all logarithmico-exponential functions. Presburger arithmetic itself is decidable ([quantifier elimination for Presburger arithmetic](../../quantifier-elimination-for-presburger-arithmetic.md)), and $\mathrm{Th}(\mathbb Z; <, +)$ is equivalent to it. For integer-valued polynomials of degree at least $2$ undecidability was classical, since they define multiplication. The source suggests, without proof, that functions of exponential growth and their inverses give decidable extensions, by ideas similar to Semënov's.

## Depends on

- [Complete theory of a first-order structure](../../../first-order-logic/theory-of-structure.md)
- [Subfield](../../../../Algebra/rings-and-fields/subfield.md)
- [Continuous map between topological spaces](../../../../Topology/topological-spaces/continuous-map.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The first-order theory of the ring of integers is undecidable](../../../proof-theory/g-del-s-incompleteness-theorems/first-order-theory-of-the-integers-is-undecidable.md)

## Expansion

In each case multiplication on $\mathbb Z$ is defined, so the theory interprets $(\mathbb Z; +, \times)$. If $f$ grows faster than every quadratic, $f$ is approximated on suitable arbitrarily long intervals by Taylor polynomials, and differentiating these polynomials defines products of arbitrarily large numbers. If $f$ grows faster than linearly but slower than quadratically, there are many intervals on which $f$ looks linear, enough to define multiplication on a restricted domain, which difference sets extend to all of $\mathbb Z \times \mathbb Z$; equidistribution results for Hardy sequences are used. In the sublinear case the inverse of $f$ can be approximated in the theory and grows faster than $x$, which yields a definable rounded Hardy field function of the first kind.

## Sources

- H. Brown and J. Konieczny, "Decidability of Extensions of Presburger Arithmetic by Hardy Field Functions", in *43rd International Symposium on Theoretical Aspects of Computer Science (STACS 2026)*, Leibniz International Proceedings in Informatics, Schloss Dagstuhl, 2026, paper 21, <https://doi.org/10.4230/LIPIcs.STACS.2026.21>, where Theorems A and B are Theorems 1.1 and 1.2 (open copy checked); numbers from arXiv:2508.19206v1, <https://arxiv.org/abs/2508.19206v1>: Section 1 (background, Theorems A and B, proof outline, future directions) and Section 2 (Hardy fields).
