# Deformations of abelian schemes

This node is still to be broken down. It covers the consequences for [abelian
schemes](abelian-scheme.md) of the [Serre–Tate theorem](serre-tate-theorem.md) and of the
[Grothendieck–Messing theorem](grothendieck-messing-theorem.md): deformations of an abelian scheme,
and of homomorphisms between abelian schemes, along a nilpotent divided power thickening are governed
by the Hodge filtration of de Rham cohomology. Let $R \to R_0$ be a surjection of rings whose kernel
$I$ carries nilpotent divided powers, and for an abelian scheme $A$ over $R$ with $A_0 = A \times_R
R_0$ identify $H^1_{\mathrm{dR}}(A/R)$ with the value on $R$ of the crystal of $A_0$. The targets are:

1. (Canonical comparison.) For abelian schemes $A$, $A'$ over $R$ lifting $A_0$, the crystal gives a
   canonical isomorphism $H^1_{\mathrm{dR}}(A/R) \cong H^1_{\mathrm{dR}}(A'/R)$ reducing to the identity
   modulo $I$, and the Hodge filtration of $A$ is a direct summand lifting that of $A_0$.
2. (Lifting abelian schemes.) Every direct summand of $H^1_{\mathrm{dR}}(A'/R)$ lifting the Hodge
   filtration of $A_0$ is the Hodge filtration of an abelian scheme $A$ over $R$ lifting $A_0$.
3. (Lifting homomorphisms.) A homomorphism $f_0 \colon A_0 \to B_0$ lifts to a homomorphism $A \to B$
   of given lifts if and only if the map that the crystal attaches to $f_0$ respects the Hodge
   filtrations, and the lift is then unique.

For rings in which $p$ is nilpotent, 1–3 follow from the Serre–Tate theorem, which reduces them to
$p$-divisible groups, and from the Grothendieck–Messing theorem with the comparison of its crystal with
de Rham cohomology (Chai–Oort, Theorem 2.4 (iii)); a good expansion has pages for this deduction and for
the compatibility of the identifications. Without the hypothesis that $p$ is nilpotent, for instance
for $R = \mathbb{Q}[\varepsilon]/(\varepsilon^2)$ and $R_0 = \mathbb{Q}$ with the square-zero ideal
$(\varepsilon)$, neither theorem applies; the statements are then those of Grothendieck's deformation
theory of abelian schemes through the Gauss–Manin connection, for which a source covering divided
power thickenings of arbitrary rings in the generality above has not been identified.

## Depends on

- [Abelian scheme](abelian-scheme.md)
- [De Rham cohomology of abelian schemes](de-rham-cohomology-of-abelian-schemes.md), for
  $H^1_{\mathrm{dR}}$, its Hodge filtration and its crystalline nature
- [Grothendieck–Messing deformation theorem](grothendieck-messing-theorem.md), for nilpotent divided
  power thickenings

## Proof depends on

- [Serre–Tate theorem](serre-tate-theorem.md)
- [Grothendieck–Messing deformation theorem](grothendieck-messing-theorem.md)

## Sources

- C.-L. Chai and F. Oort, "Moduli of abelian varieties and p-divisible groups: density of Hecke
  orbits, and a conjecture of Grothendieck", lecture notes, arXiv:math/0701479 (version 1): Theorem
  2.4 (iii)–(iv), Theorem 2.7 and Corollary 2.8.
- W. Messing, *The Crystals Associated to Barsotti–Tate Groups: with Applications to Abelian Schemes*,
  Lecture Notes in Mathematics 264, Springer, 1972, chapter "The deformation theory and applications"
  (pp. 150–174).
- N. M. Katz, "Serre–Tate local moduli", in *Surfaces algébriques*, Lecture Notes in Mathematics 868,
  Springer, 1981, 138–202: §1.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>) states 1–3, with its own admissibility condition for
  filtrations, as `GlobalTheory.Published.GrothendieckMessing.At` (`Canonical`, `LiftObj` and
  `LiftHom`), for rings in which $p$ is nilpotent as `GlobalTheory.Published.GrothendieckMessing`, and
  for all rings, without the hypothesis on $p$, as `GlobalTheory.Published.GrothendieckDeformation`.
