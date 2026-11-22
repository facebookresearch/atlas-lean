/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# `N⁰`-groups and `Ñ`-groups (Kourovka Notebook Problem 1.38)

Kourovka Notebook, Archive of Solved Problems, Problem 1.38 (Sh. S. Kemkhadze): an `N⁰`-group is a
group in which every cyclic subgroup is a term of some normal system of the group. Is every
`N⁰`-group an `Ñ`-group?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace MathlibExt.GroupTheory.NZeroGroupNTildeGroupKourovka1Problem38Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.38 (Sh. S.
Kemkhadze). UnsolvedMath record UM-00700033 (`KOU-1.38`), dataset ulamai/UnsolvedMath v1.8.0.

A normal system (Kurosh and Chernikov) is a chain of subgroups closed under arbitrary joins and
meets (hence containing `1` and `G`) whose jumps `A < B` have `A` normal in `B`. An `Ñ`-group, not
defined in the problem, is defined as in M. I. Kargapolov and Ju. I. Merzljakov, Fundamentals of the
Theory of Groups (Springer GTM 62, 1979), §22.1, the book the Notebook cites for `Ñ` in Problem
8.15: every subgroup is a member of some subnormal system (that book's name for a complete chain
with normal jumps, the Notebook's normal system). The Archive's answer exhibits free groups, which
have central systems and so are `N⁰`-groups, but are not `Ñ`-groups.
-/

/-- A normal system of `G` (Kurosh and Chernikov): a set of subgroups that is a chain under
inclusion, contains the join and the meet of each of its subsets (so it contains `⊥ = sSup ∅` and
`⊤ = sInf ∅`), and in which the lower member `A` of every jump `A < B` (no member strictly between)
is normal in `B`. -/
def IsNormalSystem {G : Type} [Group G] (S : Set (Subgroup G)) : Prop :=
  IsChain (· ≤ ·) S ∧ (∀ T ⊆ S, sSup T ∈ S ∧ sInf T ∈ S) ∧
    ∀ A ∈ S, ∀ B ∈ S, A < B → (∀ C ∈ S, ¬ (A < C ∧ C < B)) → (A.subgroupOf B).Normal

/-- `G` is an `N⁰`-group: every cyclic subgroup is a member of some normal system of `G`. -/
def IsNZeroGroup (G : Type) [Group G] : Prop :=
  ∀ g : G, ∃ S : Set (Subgroup G), IsNormalSystem S ∧ Subgroup.zpowers g ∈ S

/-- `G` is an `Ñ`-group: every subgroup is a member of some normal system of `G`. -/
def IsNTildeGroup (G : Type) [Group G] : Prop :=
  ∀ H : Subgroup G, ∃ S : Set (Subgroup G), IsNormalSystem S ∧ H ∈ S

/-- Kourovka 1.38 (Sh. S. Kemkhadze): every `N⁰`-group is an `Ñ`-group. -/
def nZeroGroupIsNTildeGroup : Prop :=
  ∀ (G : Type) [Group G], IsNZeroGroup G → IsNTildeGroup G

/--
Resolved false: the Kourovka Archive answers 1.38 "No" (Merzlyakov 1973): a group with a central
system `{Hᵢ}` is an `N⁰`-group, since `{⟨g, Hᵢ⟩}` refined by `1` and the intersections of its
subsystems is a normal system containing `⟨g⟩`; free groups have central systems but are not
`Ñ`-groups (a non-normal maximal subgroup is a term of no normal system). `Ñ` is defined as in
Kargapolov and Merzljakov, Fundamentals of the Theory of Groups, §22.1 (the Notebook's reference for
`Ñ` in Problem 8.15): every subgroup is a term of some normal system. Source: E. I. Khukhro and V.
D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.38 (Sh. S. Kemkhadze); resolution:
Yu. I. Merzlyakov (1973), as recorded in the Kourovka Archive, Problem 1.38, Archive answer: No; a
group with a central system is an N⁰-group, and free groups have central systems but are not
Ñ-groups, https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted nZeroGroupIsNTildeGroup_refuted : ¬ nZeroGroupIsNTildeGroup

end MathlibExt.GroupTheory.NZeroGroupNTildeGroupKourovka1Problem38Wanted
