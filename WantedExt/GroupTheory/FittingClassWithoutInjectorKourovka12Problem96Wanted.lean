/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A Fitting class and a non-soluble group without injectors (Kourovka Notebook Problem 12.96)

Kourovka Notebook, Archive of Solved Problems, Problem 12.96 (L. A. Shemetkov): find a non-empty
Fitting class `𝔉` and a non-soluble finite group `G` such that `G` has no `𝔉`-injectors.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.IsSubnormal
public import Mathlib.GroupTheory.Solvable

@[expose] public section

namespace MathlibExt.GroupTheory.FittingClassWithoutInjectorKourovka12Problem96Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.96 (L. A.
Shemetkov). UnsolvedMath record UM-00700913 (`KOU-12.96`), dataset ulamai/UnsolvedMath v1.8.0.

Classes of finite groups are isomorphism-closed predicates on groups in `Type` (`GroupClass`, as in
the `OpenConjectures` entries `Kourovka11Problem117` and `Kourovka12Problem35`); only their finite
members are constrained. A Fitting class is closed under normal subgroups and under products of two
normal members; non-empty means that it contains some finite group. An `𝔉`-injector of `G` is a
subgroup `V` such that `V ⊓ N` is `𝔉`-maximal in `N` for every subnormal subgroup `N` (the
definition used in `OpenConjectures` entry `Kourovka11Problem117`, which asks the open variant for
Fitting classes of soluble groups).
-/

/-- **Isomorphism-closed classes of groups (Kourovka 12.96).** A class of groups is a property of
groups that is closed under isomorphism: if a group $H$ has the property and $K$ is a group
isomorphic to $H$, then $K$ has it too.

Only finite members matter for Fitting classes and for injectors of finite groups. -/
structure GroupClass where
  /-- Membership predicate. -/
  mem : ∀ (H : Type) [Group H], Prop
  /-- Closure under isomorphism. -/
  iso : ∀ (H K : Type) [Group H] [Group K], (H ≃* K) → mem H → mem K

/-- **Fitting classes of finite groups.** A class $\mathfrak{X}$ of groups is a Fitting class of
finite groups if, for every finite group $G$, every normal subgroup of $G$ lies in $\mathfrak{X}$
whenever $G$ does, and the product $N_1 N_2$ of two normal subgroups $N_1$ and $N_2$ of $G$ lies in
$\mathfrak{X}$ whenever $N_1$ and $N_2$ do. -/
def IsFitting (X : GroupClass) : Prop :=
  (∀ (G : Type) [Group G] [Finite G] (N : Subgroup G), N.Normal → X.mem G → X.mem N) ∧
  ∀ (G : Type) [Group G] [Finite G] (N₁ N₂ : Subgroup G), N₁.Normal → N₂.Normal →
    X.mem N₁ → X.mem N₂ → X.mem ↥(N₁ ⊔ N₂)

/-- **Maximal subgroups within a class of groups.** Let $\mathfrak{X}$ be a class of groups and let
$V$ and $K$ be subgroups of a group $G$. Then $V$ is $\mathfrak{X}$-maximal in $K$ if $V \le K$,
$V$ lies in $\mathfrak{X}$, and no subgroup $W$ of $G$ with $V < W \le K$ lies in $\mathfrak{X}$. -/
def IsXMaximalIn (X : GroupClass) {G : Type} [Group G] (V K : Subgroup G) : Prop :=
  V ≤ K ∧ X.mem V ∧ ∀ W : Subgroup G, V < W → W ≤ K → ¬ X.mem W

/-- **Injectors.** Let $\mathfrak{X}$ be a class of groups and $G$ a group. A subgroup $V$ of $G$ is
an $\mathfrak{X}$-injector of $G$ if, for every subnormal subgroup $N$ of $G$, the intersection
$V \cap N$ is $\mathfrak{X}$-maximal in $N$. -/
def IsInjector (X : GroupClass) {G : Type} [Group G] (V : Subgroup G) : Prop :=
  ∀ N : Subgroup G, N.IsSubnormal → IsXMaximalIn X (V ⊓ N) N

/-- **Kourovka Problem 12.96: a Fitting class without injectors.** The statement that there are a
Fitting class $\mathfrak{X}$ of finite groups that contains at least one finite group and a finite
non-soluble group $G$ such that no subgroup of $G$ is an $\mathfrak{X}$-injector of $G$.

The problem was posed by L. A. Shemetkov. -/
def fittingClassWithoutInjectors : Prop :=
  ∃ X : GroupClass, IsFitting X ∧ (∃ (H : Type) (_ : Group H) (_ : Finite H), X.mem H) ∧
    ∃ (G : Type) (_ : Group G) (_ : Finite G), ¬ Group.IsSolvable G ∧
      ∀ V : Subgroup G, ¬ IsInjector X V

/--
**A Fitting class with no injectors in a non-soluble group.** There are a Fitting class
$\mathfrak{X}$ of finite groups that contains at least one finite group and a finite non-soluble
group $G$ such that no subgroup of $G$ is an $\mathfrak{X}$-injector of $G$.

This answers Kourovka Problem 12.96 (L. A. Shemetkov) affirmatively: the Kourovka Archive records
that E. Salomon found such a Fitting class and group; the example is presented in Section 7.1 of
Ballester-Bolinches and Ezquerro, Classes of finite groups (2006).

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory:
The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem
12.96 (L. A. Shemetkov); resolution: E. Salomon (unpublished), presented in A. Ballester-Bolinches
and L. M. Ezquerro, Classes of finite groups, Springer, 2006, Section 7.1, Kourovka Archive, Problem
12.96: found by E. Salomon.
-/
public theorem_wanted fittingClassWithoutInjectors_holds : fittingClassWithoutInjectors

end MathlibExt.GroupTheory.FittingClassWithoutInjectorKourovka12Problem96Wanted
