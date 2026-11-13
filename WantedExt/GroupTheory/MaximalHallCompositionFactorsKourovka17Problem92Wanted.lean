/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Composition factors of groups whose maximal subgroups are Hall (Kourovka Notebook Problem 17.92)

Kourovka Notebook, Archive of Solved Problems, Problem 17.92 (V. S. Monakhov): what are the
non-abelian composition factors of a finite non-soluble group all of whose maximal subgroups are
Hall subgroups?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.IsSubnormal
public import Mathlib.GroupTheory.Solvable
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

@[expose] public section

namespace MathlibExt.GroupTheory.MaximalHallCompositionFactorsKourovka17Problem92Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 17.92 (V. S.
Monakhov). UnsolvedMath record UM-00701394 (`KOU-17.92`), dataset ulamai/UnsolvedMath v1.8.0.

The answer is a set of groups, stated by two targets: every non-abelian composition factor of such a
group is one of `L₂(7)`, `L₂(11)`, `L₅(2)`, and each of the three occurs. A Hall subgroup has order
coprime to its index; maximal subgroups are coatoms; a composition factor of `G` is a group
isomorphic to a simple quotient `H/K` with `H` subnormal in `G` (`Subgroup.IsSubnormal`) and `K`
normal in `H`. `L_n(q)` is Mathlib's `Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod q)`, the
quotient `SL_n(q)/Z(SL_n(q))`.
-/

/-- **Hall subgroup (Kourovka 17.92).** A subgroup $H$ of a group $G$ is a Hall subgroup when its
order $|H|$ is coprime to its index $|G : H|$.

Here $|H|$ and $|G : H|$ are natural numbers, taken to be $0$ when infinite. -/
def IsHallSubgroup {G : Type*} [Group G] (H : Subgroup G) : Prop :=
  Nat.Coprime (Nat.card H) H.index

/-- **Composition factor of a group (Kourovka 17.92).** For groups $G$ and $S$, $S$ is a
composition factor of $G$ when there are subgroups $H$ and $K$ of $G$ such that $H$ is subnormal in
$G$, $H \cap K$ is normal in $H$, and the quotient $H/(H \cap K)$ is a simple group isomorphic to
$S$. -/
def IsCompositionFactor (G S : Type*) [Group G] [Group S] : Prop :=
  ∃ (H K : Subgroup G) (_ : (K.subgroupOf H).Normal), H.IsSubnormal ∧
    IsSimpleGroup (H ⧸ K.subgroupOf H) ∧ Nonempty (H ⧸ K.subgroupOf H ≃* S)

/-- **Non-soluble groups with Hall maximal subgroups.** A group $G$ has this property when $G$ is
not soluble and every maximal subgroup of $G$ is a Hall subgroup. -/
def IsMaximalHallNonsoluble (G : Type*) [Group G] : Prop :=
  ¬ Group.IsSolvable G ∧ ∀ M : Subgroup G, IsCoatom M → IsHallSubgroup M

/-- **Kourovka 17.92, first half: the possible composition factors.** The proposition that every
non-abelian composition factor of a finite non-soluble group all of whose maximal subgroups are
Hall subgroups is isomorphic to $L_2(7)$, $L_2(11)$ or $L_5(2)$. Here $L_n(q)$ is the projective
special linear group $\mathrm{PSL}_n(\mathbb{Z}/q\mathbb{Z})$, the quotient of
$\mathrm{SL}_n(\mathbb{Z}/q\mathbb{Z})$ by its centre. -/
def maximalHallCompositionFactorsInList : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsMaximalHallNonsoluble G →
    ∀ (S : Type) [Group S], IsCompositionFactor G S → (∃ a b : S, a * b ≠ b * a) →
      Nonempty (S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7)) ∨
        Nonempty (S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 11)) ∨
        Nonempty (S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2))

/-- **Kourovka 17.92, second half: the three factors occur.** The proposition that each of
$L_2(7)$, $L_2(11)$ and $L_5(2)$ is a composition factor of some finite non-soluble group all of
whose maximal subgroups are Hall subgroups. Here $L_n(q)$ is the projective special linear group
$\mathrm{PSL}_n(\mathbb{Z}/q\mathbb{Z})$, the quotient of $\mathrm{SL}_n(\mathbb{Z}/q\mathbb{Z})$
by its centre. -/
def maximalHallCompositionFactorsOccur : Prop :=
  (∃ (G : Type) (_ : Group G) (_ : Finite G), IsMaximalHallNonsoluble G ∧
      IsCompositionFactor G (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7))) ∧
    (∃ (G : Type) (_ : Group G) (_ : Finite G), IsMaximalHallNonsoluble G ∧
      IsCompositionFactor G (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 11))) ∧
    (∃ (G : Type) (_ : Group G) (_ : Finite G), IsMaximalHallNonsoluble G ∧
      IsCompositionFactor G (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2)))

/--
**Maslova's theorem on groups with Hall maximal subgroups.** Every non-abelian composition factor
of a finite non-soluble group all of whose maximal subgroups are Hall subgroups is isomorphic to
$L_2(7)$, $L_2(11)$ or $L_5(2)$, so the first half of the answer to Kourovka 17.92 holds. Here
$L_n(q)$ is the projective special linear group $\mathrm{PSL}_n(\mathbb{Z}/q\mathbb{Z})$, the
quotient of $\mathrm{SL}_n(\mathbb{Z}/q\mathbb{Z})$ by its centre.

Maslova (2012) proved this; the Kourovka Archive gives these three groups as the answer to 17.92.

Source:
E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook,
21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 17.92 (V. S. Monakhov);
resolution: N. V. Maslova, Siberian Math. J. 53 (2012), 853-861; N. V. Maslova and D. O. Revin,
Finite groups whose maximal subgroups have the Hall property, Siberian Adv. Math. 23 (2013), no. 3,
Maslova-Revin, Introduction (by Levchuk-Likharev and Tyutyanov, L_2(7), L_2(11) and L_5(2) are
groups all of whose maximal subgroups are Hall; by Maslova (2012) every non-abelian composition
factor of such a group is one of them, so the three groups exhaust the non-abelian composition
factors); Kourovka Archive, Problem 17.92 (Answer: L_2(7), L_2(11), L_5(2)),
https://doi.org/10.3103/S105513441303005X.
-/
public theorem_wanted maximalHallCompositionFactorsInList_holds :
    maximalHallCompositionFactorsInList

/--
**The three answer groups of Kourovka 17.92 occur.** Each of $L_2(7)$, $L_2(11)$ and $L_5(2)$ is a
composition factor of some finite non-soluble group all of whose maximal subgroups are Hall
subgroups, so the second half of the answer to Kourovka 17.92 holds. Here $L_n(q)$ is the
projective special linear group $\mathrm{PSL}_n(\mathbb{Z}/q\mathbb{Z})$, the quotient of
$\mathrm{SL}_n(\mathbb{Z}/q\mathbb{Z})$ by its centre.

Each of the three groups is itself non-soluble with all of its maximal subgroups Hall
(Levchuk-Likharev, Tyutyanov, as recalled by Maslova and Revin); with Maslova's theorem the three
groups are exactly the non-abelian composition factors.

Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 17.92 (V. S. Monakhov);
resolution: N. V. Maslova, Siberian Math. J. 53 (2012), 853-861; N. V. Maslova and D. O. Revin,
Finite groups whose maximal subgroups have the Hall property, Siberian Adv. Math. 23 (2013), no. 3,
Maslova-Revin, Introduction (by Levchuk-Likharev and Tyutyanov, L_2(7), L_2(11) and L_5(2) are
groups all of whose maximal subgroups are Hall; by Maslova (2012) every non-abelian composition
factor of such a group is one of them, so the three groups exhaust the non-abelian composition
factors); Kourovka Archive, Problem 17.92 (Answer: L_2(7), L_2(11), L_5(2)),
https://doi.org/10.3103/S105513441303005X.
-/
public theorem_wanted maximalHallCompositionFactorsOccur_holds : maximalHallCompositionFactorsOccur

end MathlibExt.GroupTheory.MaximalHallCompositionFactorsKourovka17Problem92Wanted
