# De Rham cohomology of abelian schemes

This node is still to be broken down. It covers the first de Rham cohomology $H^1 =
H^1_{\mathrm{dR}}(A/R)$ of an [abelian scheme](../abelian-scheme.md) $A$ of relative dimension $g$
over a ring $R$, its dual, the first de Rham homology $H_1 = \operatorname{Hom}_R(H^1, R)$, and
their Hodge filtrations, in the form used by the deformation theory of abelian schemes and by the
Hodge bundle on moduli spaces. Write $\omega = \omega_{A/R} = e^* \Omega^1_{A/R}$ and $A^t$ for the
dual abelian scheme. The targets are:

1. (Freeness.) Every class of $H^1$ is primitive, that is, $m^* x = p_1^* x + p_2^* x$ on $A
   \times_R A$; $H^1$ is a finite projective $R$-module of rank $2g$, and the cup product induces an
   isomorphism $\bigwedge^2 H^1 \cong H^2_{\mathrm{dR}}(A/R)$.
2. (Hodge filtration.) The Hodge filtration gives an exact sequence of finite projective modules $0
   \to \omega \to H^1 \to \operatorname{Lie}(A^t/R) \to 0$, with $\omega$ a direct summand of rank
   $g$. Dually, the annihilator $\operatorname{Fil} = \omega^\perp \subset H_1$ of $\omega$ is a
   direct summand, and $0 \to \operatorname{Lie}(A^t/R)^\vee \to H_1 \to \operatorname{Lie}(A/R) \to
   0$ with $\operatorname{Fil} = \operatorname{Lie}(A^t/R)^\vee$; the map $H_1 \to
   \operatorname{Lie}(A/R)$ is identified with the tangent vectors of $A$ along the zero section.
3. (Base change.) The formation of $H^1$ and of $\omega$ commutes with every base change $R \to R'$.
4. (Rigidity.) For a surjection $R \to R_0$ whose kernel carries nilpotent divided powers and $A_0 =
   A \times_R R_0$, the comparison map from the crystalline cohomology of $A_0$ relative to $R$ to
   $H^1$ is bijective; in particular $H^1$ depends only on $A_0$.
5. (Duality.) Let $L$ be a line bundle on $A$ and write its de Rham Chern class $c_1(L) \in
   H^2_{\mathrm{dR}}(A/R) = \bigwedge^2 H^1$ as $\sum_k a_k \wedge b_k$. The alternating form on
   **homology** $\psi_L(x, y) = \sum_k \bigl(x(a_k) y(b_k) - x(b_k) y(a_k)\bigr)$, for $x, y \in
   H_1$, vanishes on $\operatorname{Fil} \times \operatorname{Fil}$, and it is perfect when $K(L)$
   is trivial, that is, when $\varphi_L$ is an isomorphism.

The form in 5 lives on $H_1$, not on $H^1$: a class in $\bigwedge^2 H^1$ is a bilinear form on the
dual module. Dualizing turns 2 and 5 into statements about $H^1$ with annihilators, and reverses the
variance of homomorphisms ($f^* \colon H^1(B) \to H^1(A)$ against $f_* \colon H_1(A) \to H_1(B)$).

The classical sources cover these statements in different generality, and none states the whole
package 1–5 over all rings. Over a field, 1–3 follow from the degeneration of the Hodge–de Rham
spectral sequence and $H^\bullet_{\mathrm{dR}} = \bigwedge^\bullet H^1$ (van der Geer–Moonen,
Corollary (7.29)); that corollary alone does not give base change over a ring. Over any base, $H_1$
is the Lie algebra of the universal vector extension $A^\natural$ of $A$ itself, an extension of $A$
by the vector group of $R^1 f_* \mathcal{O}_A$ whose formation commutes with base change, while the
universal vector extension of $A^t$ has Lie algebra $H^1$; moreover $H^q_{\mathrm{dR}}(A/R) \cong
e^* \Omega^q_{A^\natural/R}$ for all $q$ (Mazur–Messing, I.2.6.7 and I.4.1.7, as cited by
Fonseca–Matthes, §2.2 and Remark 2.8, and by Česnavičius, §3.2). For thickenings in which $p$ is
nilpotent, Chai and Oort's Theorem 2.4 (iii) identifies the de Rham **homology** of an abelian
scheme lifting $A_0$ with the Grothendieck–Messing crystal of $A_0[p^\infty]$ evaluated on the
thickening (Messing); dualizing gives $H^1$ as the dual of the evaluated Barsotti–Tate crystal. The
rigidity 4 is stated with the geometric crystalline cohomology of $A_0$ relative to $R$, and
identifying that with the dual Barsotti–Tate crystal is a separate input, not a clause of Chai and
Oort's theorem: it needs the comparison of crystalline with de Rham cohomology for a smooth lift
(Stacks Project, *Crystalline Cohomology*, §§20–21, Tag 07LG) and the compatibility of the resulting
comparison maps. Rings in which $p$ is nilpotent and $\mathbb{Q}$-algebras do not exhaust the
thickenings of 4: $\mathbb{Z}[\varepsilon]/(\varepsilon^2) \to \mathbb{Z}$, with the divided powers
of its square-zero ideal, is in neither case, and such mixed thickenings belong to the pending
all-ring target. A good expansion has pages for: the Hodge–de Rham spectral sequence of an abelian
scheme over a ring and its degeneration, with base change; universal vector extensions and the
identifications above; the crystalline comparison for $p$-nilpotent thickenings, with the duality
between homology and cohomology and the identification of the dual Barsotti–Tate crystal with the
geometric crystalline cohomology of $A_0$; the Gauss–Manin connection and its integration for
divided power thickenings of $\mathbb{Q}$-algebras; the mixed thickenings, for which no source has
been identified; and the polarization form of 5 with its isotropy and perfectness.

## Depends on

- [Abelian scheme](../abelian-scheme.md)
- [Dual abelian scheme](../dual-abelian-scheme.md), for $\operatorname{Lie}(A^t/R)$ and $\varphi_L$

## Sources

- B. Mazur and W. Messing, *Universal Extensions and One Dimensional Crystalline Cohomology*,
  Lecture Notes in Mathematics 370, Springer, 1974: I.2.6.7 and I.4.1.7, as cited by Fonseca–Matthes
  and by Česnavičius.
- T. J. Fonseca and N. Matthes, "A note on the Gauss–Manin connection for abelian schemes",
  arXiv:2201.06402 (version 2): introduction, p. 1 ($\operatorname{Lie}_S A^\natural \cong
  H^1_{\mathrm{dR}}(A/S)^\vee$), §2.2 with (2.1) (universal vector extension and base change) and
  Remark 2.8.
- K. Česnavičius, "The Manin constant in the semistable case",
  <https://www.math.uni-bonn.de/people/kestutis/Manin-semistable.pdf>: §3.2, the paragraph after
  (3.2.1) (the universal vector extension of the dual and $H^1_{\mathrm{dR}}$).
- W. Messing, *The Crystals Associated to Barsotti–Tate Groups: with Applications to Abelian
  Schemes*, Lecture Notes in Mathematics 264, Springer, 1972, chapter "The deformation theory and
  applications".
- C.-L. Chai and F. Oort, "Moduli of abelian varieties and p-divisible groups: density of Hecke
  orbits, and a conjecture of Grothendieck", lecture notes, arXiv:math/0701479 (version 1): Theorem
  2.4 (iii) (the comparison of the crystal with de Rham **homology** and its Hodge filtration, for
  $p$-nilpotent thickenings).
- The Stacks Project, <https://stacks.math.columbia.edu>, *Crystalline Cohomology*, §§20–21 (Tag
  07LG: crystalline cohomology of a smooth lift computed by its de Rham complex).
- G. van der Geer and B. Moonen, *Abelian Varieties*, book draft, Chapter VII, "Duality",
  <https://www.math.ru.nl/personal/bmoonen/BookAV/DualAV2.pdf>: the Hodge–de Rham spectral sequence
  and Corollary (7.29), pp. 107–108.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states 1–5 over every ring as `GlobalTheory.Published.AbelianDeRham`, the conjunction of `Free`,
  `Hodge`, `BaseChange`, `Rigid` and `Duality`: its de Rham module `HdR` is the dual of the
  primitive part of $H^1$, its filtration `Fil` is the annihilator of the primitive Hodge submodule,
  and `IsPolForm` evaluates a wedge representative of $c_1(L)$ on two homology classes, as in 5;
  `Duality` asserts isotropy for every such form and perfectness under `KTriv` (trivial $K(L)$). No
  published source stating this package over all rings has been identified.
