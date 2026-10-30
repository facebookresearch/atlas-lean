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

/-- A Hall subgroup: its order is coprime to its index. -/
def IsHallSubgroup {G : Type*} [Group G] (H : Subgroup G) : Prop :=
  Nat.Coprime (Nat.card H) H.index

/-- `S` is a composition factor of `G`: `S ≅ H/K` for a subnormal subgroup `H` of `G` and a normal
subgroup `K` of `H` with `H/K` simple. -/
def IsCompositionFactor (G S : Type*) [Group G] [Group S] : Prop :=
  ∃ (H K : Subgroup G) (_ : (K.subgroupOf H).Normal), H.IsSubnormal ∧
    IsSimpleGroup (H ⧸ K.subgroupOf H) ∧ Nonempty (H ⧸ K.subgroupOf H ≃* S)

/-- `G` is non-soluble and all of its maximal subgroups are Hall subgroups. -/
def IsMaximalHallNonsoluble (G : Type*) [Group G] : Prop :=
  ¬ Group.IsSolvable G ∧ ∀ M : Subgroup G, IsCoatom M → IsHallSubgroup M

/-- Kourovka 17.92 (V. S. Monakhov), first half of the answer: every non-abelian composition factor
of a finite non-soluble group all of whose maximal subgroups are Hall subgroups is isomorphic to
`L₂(7)`, `L₂(11)` or `L₅(2)`. -/
def maximalHallCompositionFactorsInList : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsMaximalHallNonsoluble G →
    ∀ (S : Type) [Group S], IsCompositionFactor G S → (∃ a b : S, a * b ≠ b * a) →
      Nonempty (S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7)) ∨
        Nonempty (S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 11)) ∨
        Nonempty (S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2))

/-- Kourovka 17.92 (V. S. Monakhov), second half of the answer: each of `L₂(7)`, `L₂(11)` and
`L₅(2)` is a composition factor of some finite non-soluble group all of whose maximal subgroups are
Hall subgroups. -/
def maximalHallCompositionFactorsOccur : Prop :=
  (∃ (G : Type) (_ : Group G) (_ : Finite G), IsMaximalHallNonsoluble G ∧
      IsCompositionFactor G (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7))) ∧
    (∃ (G : Type) (_ : Group G) (_ : Finite G), IsMaximalHallNonsoluble G ∧
      IsCompositionFactor G (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 11))) ∧
    (∃ (G : Type) (_ : Group G) (_ : Finite G), IsMaximalHallNonsoluble G ∧
      IsCompositionFactor G (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2)))

/--
Resolved true: Maslova (2012) proves that every non-abelian composition factor of a finite
non-soluble group all of whose maximal subgroups are Hall subgroups is isomorphic to `L₂(7)`,
`L₂(11)` or `L₅(2)`; the Kourovka Archive gives these three groups as the answer to 17.92. Source:
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
Resolved true: `L₂(7)`, `L₂(11)` and `L₅(2)` are themselves non-soluble groups all of whose maximal
subgroups are Hall subgroups (Levchuk-Likharev, Tyutyanov, as recalled by Maslova and Revin), so
each is a composition factor of such a group; with Maslova's theorem the three groups are exactly
the non-abelian composition factors, the answer recorded by the Kourovka Archive. Source: E. I.
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
