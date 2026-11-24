# Crystalline nature of the de Rham cohomology of abelian schemes

This node is still to be broken down: the statement is precise, but its proof is not, and for
thickenings in which $p$ is not nilpotent no source covering the statement has been identified.

Let $R \to R_0$ be a surjection of rings whose kernel carries nilpotent divided powers, $A$ an
[abelian scheme](../abelian-scheme.md) over $R$ and $A_0 = A \times_R R_0$. Then the comparison map
from the crystalline cohomology of $A_0$ relative to $R$ to the first de Rham cohomology $H^1 =
H^1_{\mathrm{dR}}(A/R)$ of the page on
[de Rham cohomology of abelian schemes](de-rham-cohomology-of-abelian-schemes.md) is bijective; in
particular $H^1$ depends only on $A_0$.

For thickenings in which $p$ is nilpotent, Chai and Oort's Theorem 2.4 (iii) identifies the de Rham
**homology** of an abelian scheme lifting $A_0$ with the Grothendieck–Messing crystal of
$A_0[p^\infty]$ evaluated on the thickening, which is item (3) of the
[Grothendieck–Messing theorem](grothendieck-messing-theorem.md); dualizing gives $H^1$ as the dual
of the evaluated Barsotti–Tate crystal. The statement above uses the geometric crystalline
cohomology of $A_0$ relative to $R$, and identifying that with the dual Barsotti–Tate crystal is a
separate input, not a clause of Chai and Oort's theorem: it needs the comparison of crystalline with
de Rham cohomology for a smooth lift (Stacks Project, *Crystalline Cohomology*, Tags 07LG, 07LH and
07MW) and the compatibility of the resulting comparison maps. Rings in which $p$ is nilpotent and
$\mathbb{Q}$-algebras do not exhaust these thickenings: $\mathbb{Z}[\varepsilon]/(\varepsilon^2) \to
\mathbb{Z}$, with the divided powers of its square-zero ideal, is in neither case.

A good expansion has pages for: the crystalline comparison for $p$-nilpotent thickenings, with the
duality between homology and cohomology and the identification of the dual Barsotti–Tate crystal
with the geometric crystalline cohomology of $A_0$; the Gauss–Manin connection and its integration
for divided power thickenings of $\mathbb{Q}$-algebras; and the mixed thickenings, for which no
source has been identified.

## Depends on

- [Abelian scheme](../abelian-scheme.md)
- [De Rham cohomology of abelian schemes](de-rham-cohomology-of-abelian-schemes.md), for
  $H^1_{\mathrm{dR}}(A/R)$

## Proof depends on

- [Grothendieck–Messing deformation theorem](grothendieck-messing-theorem.md), for the
  identification of de Rham homology with the Grothendieck–Messing crystal for $p$-nilpotent
  thickenings (its item (3); Chai–Oort, Theorem 2.4 (iii))
- [De Rham cohomology of abelian schemes](de-rham-cohomology-of-abelian-schemes.md), for the duality
  between $H_1$ and $H^1$ and their Hodge filtrations

The other steps of its proof are not pages yet: the comparison of crystalline and de Rham cohomology
for a smooth lift and the compatibility of the comparison maps (Stacks Project, Tags 07LH and 07MW),
the Gauss–Manin connection for divided power thickenings of $\mathbb{Q}$-algebras, and the mixed
thickenings, for which no source has been identified.

## Sources

- C.-L. Chai and F. Oort, "Moduli of abelian varieties and p-divisible groups: density of Hecke
  orbits, and a conjecture of Grothendieck", lecture notes, arXiv:math/0701479 (version 1): Theorem
  2.4 (iii) (the comparison of the crystal with de Rham **homology** and its Hodge filtration, for
  $p$-nilpotent thickenings).
- W. Messing, *The Crystals Associated to Barsotti–Tate Groups: with Applications to Abelian
  Schemes*, Lecture Notes in Mathematics 264, Springer, 1972, chapter "The deformation theory and
  applications".
- The Stacks Project, *Crystalline Cohomology*, Proposition 60.21.3,
  <https://stacks.math.columbia.edu/tag/07LG>, Lemma 60.21.4,
  <https://stacks.math.columbia.edu/tag/07LH> (crystalline cohomology in the affine case through a
  smooth lift), and Remark 60.24.11, <https://stacks.math.columbia.edu/tag/07MW> (comparison with
  the de Rham complex of a smooth lift).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states the target as the clause `Rigid` of `GlobalTheory.Published.AbelianDeRham`, over every
  ring.
