# Crystalline nature of the de Rham cohomology of abelian schemes

This node is still to be broken down: its geometric statement has a source, Masullo's comparison
theorem, and its identification with the form that Alpöge's library states is open.

Let $R \to R_0$ be a surjection of rings whose kernel $I$ carries nilpotent divided powers, $A$ an
[abelian scheme](../abelian-scheme.md) over $R$ and $A_0 = A \times_R R_0$. Then the comparison map
from the first crystalline cohomology $H^1_{\mathrm{cris}}(A_0/R)$ of $A_0$ relative to $R$, with
coefficients in the structure sheaf, to the first de Rham cohomology $H^1 = H^1_{\mathrm{dR}}(A/R)$
of the page on [de Rham cohomology of abelian schemes](de-rham-cohomology-of-abelian-schemes.md) is
bijective; in particular $H^1$ depends only on $A_0$.

This is the degree-one case of Masullo's comparison theorem over general divided power bases
(Theorem 6.2.1), for the closed immersion of $A_0$ into the smooth $R$-scheme $A$ and the structure
crystal. As $A$ is flat over $R$, the divided powers of $I$ extend to the ideal $I \mathcal{O}_A$ of
$A_0$, so the divided power envelope of $A_0$ in $A$ is $A$ itself; as these divided powers are
nilpotent, its pd-adic completion is $\mathcal{O}_A$, and the completed de Rham complex of the
theorem is the de Rham complex of $A$ over $R$. Masullo's crystalline site (Definition 6.1.1), whose
thickenings $(U, T, \delta)$ satisfy $n!\, J^{[n]} = 0$ locally, allows any divided power base:
there is no hypothesis that $p$ be nilpotent, and the thickening
$\mathbb{Z}[\varepsilon]/(\varepsilon^2) \to \mathbb{Z}$, with the divided powers of its square-zero
ideal, in which neither $p$ is nilpotent nor $\mathbb{Q} \subseteq R$, is covered. When $p$ is
nilpotent in $R$ the comparison is also in the Stacks Project (Tag 07MW), and Chai and Oort's
Theorem 2.4 (iii) identifies further the de Rham **homology** of a lift with the
Grothendieck–Messing crystal of $A_0[p^\infty]$, item (3) of the
[Grothendieck–Messing theorem](grothendieck-messing-theorem.md); that identification with the dual
Barsotti–Tate crystal is a further statement, not needed for the comparison above.

Alpöge's library states the target in a different model, as the clause `Rigid` of
`GlobalTheory.Published.AbelianDeRham`. Its crystalline cohomology is defined with test rings whose
divided power ideals are uniformly nilpotent, rather than on Masullo's site; it concerns primitive
classes; and the map asserted to be bijective, `(liftMor κ h).pull`, is the restriction from the
primitive cohomology of the lift to the primitive crystalline cohomology of the reduction, the map
`crysToDR` being its dual on homology. No source identifies these models and maps with the geometric
comparison above; that identification is part of this target.

## Depends on

- [Abelian scheme](../abelian-scheme.md)
- [De Rham cohomology of abelian schemes](de-rham-cohomology-of-abelian-schemes.md), for
  $H^1_{\mathrm{dR}}(A/R)$
- [Grothendieck–Messing deformation theorem](grothendieck-messing-theorem.md), for the definition of a
  nilpotent divided power thickening

## Proof depends on

Its proof uses the inputs listed under Expansion.

## Expansion

A good expansion has pages for: Masullo's crystalline site and his comparison theorem (Definition
6.1.1, Theorem 6.2.1), with the computation of the divided power envelope of $A_0$ in a smooth lift
and of its pd-adic completion; and the identification of the cohomology of primitive classes and of
the pullback map of Alpöge's library with that comparison, including its compatibility with the
group law.

## Sources

- A. M. Masullo, "Crystalline cohomology over general bases", arXiv:2011.11182 (version 1),
  <https://arxiv.org/abs/2011.11182v1>: Definition 6.1.1 (the crystalline site over a general
  divided power base), p. 29, and Theorem 6.2.1 (the comparison theorem), with Corollary 6.2.4, pp.
  31–32.
- The Stacks Project, *Crystalline Cohomology*, Proposition 60.21.3,
  <https://stacks.math.columbia.edu/tag/07LG>, Lemma 60.21.4,
  <https://stacks.math.columbia.edu/tag/07LH> (crystalline cohomology in the affine case through a
  smooth lift), and Remark 60.24.11, <https://stacks.math.columbia.edu/tag/07MW> (comparison with
  the de Rham complex of a smooth lift).
- C.-L. Chai and F. Oort, "Moduli of abelian varieties and p-divisible groups: density of Hecke
  orbits, and a conjecture of Grothendieck", lecture notes, arXiv:math/0701479 (version 1): Theorem
  2.4 (iii) (the comparison of the crystal with de Rham **homology** and its Hodge filtration, for
  $p$-nilpotent thickenings).
- W. Messing, *The Crystals Associated to Barsotti–Tate Groups: with Applications to Abelian
  Schemes*, Lecture Notes in Mathematics 264, Springer, 1972, chapter "The deformation theory and
  applications".
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states the target as the clause `Rigid` of `GlobalTheory.Published.AbelianDeRham`
  (`PublishedTheorems/Divisors₂/CrysToDRBijective.lean`), over every ring, with `liftMor` and
  `crysToDR` defined in `Definitions/Divisors/IsKSValueOneOfRetraction.lean`.
