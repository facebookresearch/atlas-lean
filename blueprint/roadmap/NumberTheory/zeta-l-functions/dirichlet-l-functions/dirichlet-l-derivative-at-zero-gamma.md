# The derivative at $s = 0$ of a Dirichlet $L$-function through the gamma function

Let $k \ge 2$, let $\chi$ be a Dirichlet character modulo $k$ other than the principal character, and let
$L(s, \chi)$ be the entire continuation of $\sum_{n \ge 1} \chi(n) n^{-s}$ $(\operatorname{Re} s > 1)$. Then

$$L(0, \chi) = -\frac{1}{k} \sum_{r=1}^{k-1} r \chi(r), \qquad L'(0, \chi) = \sum_{r=1}^{k-1} \chi(r) \log \Gamma\!\left(\frac{r}{k}\right) - L(0, \chi) \log k.$$

Indeed $L(s, \chi) = k^{-s} \sum_{r=1}^{k-1} \chi(r) \zeta(s, r/k)$ for all $s \neq 1$, where $\zeta(s, a)$ is the Hurwitz zeta
function, as one sees by grouping the terms of the Dirichlet series by residue classes modulo $k$ when
$\operatorname{Re} s > 1$, and then by the [identity theorem](../../../Geometry/complex-and-symplectic-geometry/identity-and-open-mapping-theorems-for-holomorph/holomorphic-identity-on-connected-comple.md) on $\mathbb{C} \setminus \{1\}$. Differentiating at $s = 0$ and inserting
[Lerch's formulas](lerch-formula-hurwitz-zeta.md) $\zeta(0, a) = \frac{1}{2} - a$ and
$\frac{\partial \zeta}{\partial s}(0, a) = \log \Gamma(a) - \frac{1}{2} \log(2\pi)$ gives both formulas, because
$S = \sum_{r=1}^{k-1} \chi(r) = 0$ for a non-principal character: choosing $u$ prime to $k$ with $\chi(u) \neq 1$,
multiplication by $u$ permutes the residues prime to $k$, at which alone $\chi$ is nonzero, so $S = \chi(u) S$, whence $S = 0$. (The computation is carried out here; the
sources give its two ingredients.)

## Depends on

- [Dirichlet character of a given modulus](conductors-and-primitive-dirichlet-characters/is-dirichlet-character-modulus.md), for Dirichlet characters modulo $k$

## Proof depends on

- [Lerch's formula for the Hurwitz zeta function at $s = 0$](lerch-formula-hurwitz-zeta.md)
- [Identity theorem for holomorphic maps](../../../Geometry/complex-and-symplectic-geometry/identity-and-open-mapping-theorems-for-holomorph/holomorphic-identity-on-connected-comple.md), for extending the expression through the Hurwitz zeta function from $\operatorname{Re} s > 1$

## Sources

- F. W. J. Olver et al. (eds.), *NIST Digital Library of Mathematical Functions*, Version 1.2.8 of
  2026-09-15, <https://dlmf.nist.gov/25.15>: equation 25.15.3,
  $L(s, \chi) = k^{-s} \sum_{r=1}^{k-1} \chi(r) \zeta(s, r/k)$ (at $s = 1$ the right-hand side has a removable singularity when
  $\chi$ is not principal), and the
  statement before 25.15.2 that $L(s, \chi)$ is then entire; <https://dlmf.nist.gov/25.11>, equations 25.11.13 and
  25.11.18.
- M. Kaneko, *A generalization of the Chowla–Selberg formula and the zeta functions of quadratic
  orders*, Proc. Japan Acad. 66, Ser. A (1990), 201–203,
  <https://www2.math.kyushu-u.ac.jp/~mkaneko/papers/07Chowla-Selberg.pdf>, Section 1: the proof of the
  Chowla–Selberg formula uses "a formula relating $L'(0, \chi)$ with gamma function".
