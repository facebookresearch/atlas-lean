/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Isomorphic simple maximal subgroups (Kourovka Notebook Problem 18.115)

Kourovka Notebook, Archive of Solved Problems, Problem 18.115 (P. Schmid): let `G` be a finite
simple group and `X`, `Y` isomorphic simple maximal subgroups of `G`. Are `X` and `Y` conjugate in
`Aut G`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Finite.Defs
public import Mathlib.GroupTheory.Subgroup.Simple

@[expose] public section

namespace MathlibExt.GroupTheory.IsomorphicSimpleMaximalSubgroupsKourovka18Problem115Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 18.115 (P.
Schmid). UnsolvedMath record UM-00701543 (`KOU-18.115`), dataset ulamai/UnsolvedMath v1.8.0.

Maximal subgroups are coatoms of the subgroup lattice; conjugacy in `Aut G` means `φ(X) = Y` for
some `φ : G ≃* G`. A finite simple group with a simple maximal subgroup is non-abelian, so the
cyclic simple groups (whose only maximal subgroup is trivial) impose nothing.
-/

/-- **Schmid's question on isomorphic simple maximal subgroups (Kourovka 18.115).** The statement
that in every finite simple group $G$, any two isomorphic maximal subgroups $X$ and $Y$ that are
themselves simple groups are conjugate in $\operatorname{Aut} G$, that is, $\varphi(X) = Y$ for
some automorphism $\varphi$ of $G$. -/
def isomorphicSimpleMaximalSubgroupsAutConjugate : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
    ∀ X Y : Subgroup G, IsCoatom X → IsCoatom Y → IsSimpleGroup X → IsSimpleGroup Y →
      Nonempty (X ≃* Y) → ∃ φ : MulAut G, X.map φ.toMonoidHom = Y

/--
**Isomorphic simple maximal subgroups need not be conjugate under automorphisms.** There are a
finite simple group $G$ and isomorphic maximal subgroups $X$ and $Y$ of $G$, both simple groups,
such that no automorphism $\varphi$ of $G$ satisfies $\varphi(X) = Y$. That is, the answer to
Kourovka Problem 18.115 is negative.

The Kourovka Archive answers 18.115 "No, not always": there are two $\operatorname{Aut} G$-classes
of $M_{12}$ in $E_6(5)$ (Kleidman–Wilson, 1990), and Craven (2023) found two classes of
$\mathrm{PSL}_2(11)$ and two of $\mathrm{PSL}_2(19)$ in $E_6(q)$ for certain $q$.

Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Archive of Solved Problems, Problem 18.115 (P. Schmid); resolution: P. B. Kleidman and R. A. Wilson,
J. London Math. Soc. (2) 42 (1990), 555-561; D. A. Craven, Invent. Math. 234 (2023), no. 2, 637-719,
Kourovka Archive, Problem 18.115: No, not always; two Aut G-classes of M_12 in E_6(5)
(Kleidman-Wilson), and two classes of PSL_2(11) and of PSL_2(19) in E_6(q) for certain q (Craven),
https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted isomorphicSimpleMaximalSubgroupsAutConjugate_refuted :
    ¬ isomorphicSimpleMaximalSubgroupsAutConjugate

end MathlibExt.GroupTheory.IsomorphicSimpleMaximalSubgroupsKourovka18Problem115Wanted
