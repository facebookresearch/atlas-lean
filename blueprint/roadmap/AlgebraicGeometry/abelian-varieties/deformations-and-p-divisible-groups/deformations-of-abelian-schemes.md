# Deformations of abelian schemes

This node is still to be broken down. It covers the consequences for
[abelian schemes](../abelian-scheme.md) of the [Serre–Tate theorem](serre-tate-theorem.md) and of
the [Grothendieck–Messing theorem](grothendieck-messing-theorem.md): deformations of an abelian
scheme, and of homomorphisms between abelian schemes, along a nilpotent divided power thickening are
governed by the Hodge filtration of de Rham homology. Let $R \to R_0$ be a surjection of rings whose
kernel $I$ carries nilpotent divided powers. For an abelian scheme $A$ over $R$ with $A_0 = A
\times_R R_0$, let $H_1(A) = H_1^{\mathrm{dR}}(A/R)$ be the de Rham homology, identified with the
value on $R$ of the crystal of $A_0$, and $\operatorname{Fil}(A) = \operatorname{Lie}(A^t/R)^\vee
\subset H_1(A)$ its Hodge filtration ([de Rham cohomology of abelian
schemes](de-rham-cohomology-of-abelian-schemes.md), item 2). The targets are:

1. (Canonical comparison.) For abelian schemes $A$, $A'$ over $R$ lifting $A_0$, the crystal gives a
   canonical isomorphism $H_1(A) \cong H_1(A')$ reducing to the identity modulo $I$, and
   $\operatorname{Fil}(A)$ is a direct summand whose reduction modulo $I$ is
   $\operatorname{Fil}(A_0)$.
2. (Lifting abelian schemes.) For a lift $A'$ of $A_0$, every direct summand $F \subset H_1(A')$
   whose reduction is $\operatorname{Fil}(A_0)$ is, through the isomorphism of 1, the Hodge
   filtration of an abelian scheme $A$ over $R$ lifting $A_0$.
3. (Lifting homomorphisms.) A homomorphism $f_0 \colon A_0 \to B_0$ lifts to a homomorphism $A \to
   B$ of given lifts if and only if the covariant map $f_{0*} \colon H_1(A) \to H_1(B)$ that the
   crystal attaches to $f_0$ sends $\operatorname{Fil}(A)$ into $\operatorname{Fil}(B)$, and the
   lift is then unique.

In cohomology the same statements read with the annihilators $\omega_A \subset H^1(A)$ and the
contravariant maps $f_0^*$.

For rings in which $p$ is nilpotent, 1–3 follow from the Serre–Tate theorem, in the affine form of
Katz's Theorem 1.2.1, which allows any nilpotent ideal $I$ without a coherence condition, by
reduction to $p$-divisible groups, and from the Grothendieck–Messing theorem with the comparison of
its crystal with de Rham homology (Chai–Oort, Theorem 2.4 (iii)–(iv)); a good expansion has pages
for this deduction and for the compatibility of the identifications. Without the hypothesis that $p$
is nilpotent, for instance for $R = \mathbb{Q}[\varepsilon]/(\varepsilon^2)$ and $R_0 = \mathbb{Q}$
with the square-zero ideal $(\varepsilon)$, neither theorem applies; the statements are then those
of Grothendieck's deformation theory of abelian schemes through the Gauss–Manin connection, for
which a source covering divided power thickenings of arbitrary rings in the generality above has not
been identified; only the comparison in 1 holds in this generality, through the geometric comparison
of the node on the
[crystalline nature of the de Rham cohomology of abelian schemes](crystalline-nature-of-the-de-rham-cohomology-of-abelian-schemes.md)
(Masullo, Theorem 6.2.1). This generalization is recorded here as an open target, not as a
consequence of the $p$-nilpotent case.

## Depends on

- [Abelian scheme](../abelian-scheme.md)
- [De Rham cohomology of abelian schemes](de-rham-cohomology-of-abelian-schemes.md), for the de Rham
  homology $H_1$ and its filtration $\operatorname{Fil} = \omega^\perp$ (item 2)
- [Crystalline nature of the de Rham cohomology of abelian schemes](crystalline-nature-of-the-de-rham-cohomology-of-abelian-schemes.md),
  for the crystalline cohomology of $A_0$, through which 1 compares the de Rham homologies of two
  lifts
- [Grothendieck–Messing deformation theorem](grothendieck-messing-theorem.md), for nilpotent divided
  power thickenings

## Proof depends on

- [Serre–Tate theorem](serre-tate-theorem.md)
- [Grothendieck–Messing deformation theorem](grothendieck-messing-theorem.md)
- [Crystalline nature of the de Rham cohomology of abelian schemes](crystalline-nature-of-the-de-rham-cohomology-of-abelian-schemes.md),
  for the comparison in 1 over every ring of the statement: the de Rham homologies of two lifts are
  both dual to the first crystalline cohomology of $A_0$

## Sources

- C.-L. Chai and F. Oort, "Moduli of abelian varieties and p-divisible groups: density of Hecke
  orbits, and a conjecture of Grothendieck", lecture notes, arXiv:math/0701479 (version 1): Theorem
  2.4 (iii)–(iv), Theorem 2.7 and Corollary 2.8.
- W. Messing, *The Crystals Associated to Barsotti–Tate Groups: with Applications to Abelian
  Schemes*, Lecture Notes in Mathematics 264, Springer, 1972, chapter "The deformation theory and
  applications" (pp. 150–174).
- N. M. Katz, "Serre–Tate local moduli", in *Surfaces algébriques*, Lecture Notes in Mathematics
  868, Springer, 1981, 138–202: §1, Theorem 1.2.1 (a ring in which $p$ is nilpotent and a nilpotent
  ideal), p. 144.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states 1–3 as `GlobalTheory.Published.GrothendieckMessing.At` (`Canonical`, `LiftObj` and
  `LiftHom`), on its module `HdR`, the dual of the primitive part of $H^1$, with the annihilator
  filtration `Fil` and the covariant map `push` for homomorphisms, as in 1–3 above; for rings in
  which $p$ is nilpotent as `GlobalTheory.Published.GrothendieckMessing`, and for all rings, without
  the hypothesis on $p$, as `GlobalTheory.Published.GrothendieckDeformation`.
