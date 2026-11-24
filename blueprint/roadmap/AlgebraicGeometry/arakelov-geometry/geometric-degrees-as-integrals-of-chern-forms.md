# Geometric degrees as integrals of first Chern forms

This node is still to be broken down: the statement is precise, but its proof is not.

Let $V$ be a projective complex variety, possibly singular, $Z \subseteq V$ an integral closed
subvariety of dimension $k$, and $\bar L_1, \dots, \bar L_k$ holomorphic line bundles on $V$ with
smooth hermitian metrics, smooth in the sense of local ambient extensions. Then the form $c_1(\bar
L_1) \wedge \dots \wedge c_1(\bar L_k)$ restricted to the regular locus $Z_{\mathrm{reg}}$ is
integrable, and

$$\int_{Z_{\mathrm{reg}}} c_1(\bar L_1) \wedge \dots \wedge c_1(\bar L_k) = \deg\bigl( c_1(L_1) \cdots
c_1(L_k) \mid Z \bigr),$$

the intersection number of the line bundles on $Z$.

Applied to $V = X(\mathbb{C})$ for a projective flat scheme $X$ over $\mathbb{Z}$ (a proper one need
not have projective complex points; it is reduced to this case by a projective modification, Chow's
lemma) and to the complex points of a horizontal cycle, it computes the archimedean term of
Chambert-Loir's recursion for arithmetic degrees only for a **constant** metric on the trivial line
bundle. For $\lVert 1 \rVert = e^{-u}$ with a variable smooth $u$, that term is the weighted
integral $\int_{Z(\mathbb{C})} u\, c_1(\bar L_1) \wedge \dots \wedge c_1(\bar L_k)$ (Chambert-Loir
(2.5.1)), which is not the degree: for $Z = \mathbb{P}^1$, $\bar L_1 = \mathcal{O}(1)$ with
Fubini–Study curvature of total mass $1$ and a nonconstant $u$ of mean zero, it vanishes while the
degree is $1$. A constant $u = t$ gives $t \deg(c_1(L_1) \cdots c_1(L_k) \mid Z)$, which is the
effect of a constant rescaling of a metric on an arithmetic intersection number.

A good expansion proves the identity by pulling back to a smooth projective resolution $\tilde Z \to
Z$, which leaves both sides unchanged (proper birational push-forward gives the same cycle and the
same integral, and the integrand is integrable by local ambient smoothness and compactness); on
$\tilde Z$, by the Chern–Weil theorem that $c_1(\bar L)$ represents the first Chern class of $L$ in
de Rham cohomology (Demailly, Chapter V, Theorem 9.5) and the compatibility of algebraic and
topological first Chern classes, or by induction on $k$ with divisors of sections and the
Poincaré–Lelong formula, and the projection formula in degree one. On a singular ambient $V$ the
fundamental class of $Z$ is a homology class, or the current $[Z]$ of integration over
$Z_{\mathrm{reg}}$, closed and positive of locally finite mass by Lelong's theorem, not a cohomology
class of $V$.

## Depends on

- [Arithmetic varieties and hermitian vector bundles](arithmetic-variety.md), for metrics smooth in
  the sense of local ambient extensions

## Proof depends on

- [Resolution of singularities of quasi-projective varieties](../birational-geometry/resolution-of-singularities/resolution-of-singularities-of-quasi-projective-varieties.md),
  for the resolution $\tilde Z \to Z$
- [Currents of integration and the support theorems](../birational-geometry/currents-of-integration.md),
  for Lelong's theorem on $[Z]$
- [Poincaré–Lelong formula](../birational-geometry/poincare-lelong-formula.md), for the induction by
  divisors of sections

## Sources

- A. Chambert-Loir, "Arakelov geometry, heights, equidistribution, and the Bogomolov conjecture",
  arXiv:1904.05630v3 (2020), <https://arxiv.org/abs/1904.05630v3>: 2.3 (smooth metrics on singular
  complex spaces) and Theorem (2.5), with (2.5.1), pp. 2–4.
- J.-P. Demailly, *Complex Analytic and Differential Geometry*, version of 21 June 2012,
  <https://www-fourier.univ-grenoble-alpes.fr/~demailly/manuscripts/agbook.pdf>: Chapter III,
  (2.5)–(2.7) (currents of integration on analytic sets), p. 140; Chapter V, Theorem 9.5
  (Chern–Weil), p. 265.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  uses the integrability and the identity, for powers of one line bundle with a smooth metric,
  inside `GlobalTheory.Published.ArDegree`.
