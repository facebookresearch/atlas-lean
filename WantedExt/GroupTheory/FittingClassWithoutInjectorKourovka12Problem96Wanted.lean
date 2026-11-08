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

/-- A class of groups closed under isomorphism, given by a membership predicate on groups in
`Type`; only its finite members matter below. -/
structure GroupClass where
  /-- Membership predicate. -/
  mem : ∀ (H : Type) [Group H], Prop
  /-- Closure under isomorphism. -/
  iso : ∀ (H K : Type) [Group H] [Group K], (H ≃* K) → mem H → mem K

/-- A Fitting class of finite groups: closed under normal subgroups and under products of two
normal subgroups belonging to the class. -/
def IsFitting (X : GroupClass) : Prop :=
  (∀ (G : Type) [Group G] [Finite G] (N : Subgroup G), N.Normal → X.mem G → X.mem N) ∧
  ∀ (G : Type) [Group G] [Finite G] (N₁ N₂ : Subgroup G), N₁.Normal → N₂.Normal →
    X.mem N₁ → X.mem N₂ → X.mem ↥(N₁ ⊔ N₂)

/-- `V` is `X`-maximal in `K`: `V ≤ K`, `V ∈ X`, and no `X`-subgroup of `K` properly contains
`V`. -/
def IsXMaximalIn (X : GroupClass) {G : Type} [Group G] (V K : Subgroup G) : Prop :=
  V ≤ K ∧ X.mem V ∧ ∀ W : Subgroup G, V < W → W ≤ K → ¬ X.mem W

/-- `V` is an `X`-injector of `G`: `V ⊓ N` is `X`-maximal in `N` for every subnormal subgroup
`N` of `G`. -/
def IsInjector (X : GroupClass) {G : Type} [Group G] (V : Subgroup G) : Prop :=
  ∀ N : Subgroup G, N.IsSubnormal → IsXMaximalIn X (V ⊓ N) N

/-- Kourovka 12.96 (L. A. Shemetkov): there are a non-empty Fitting class `X` of finite groups
and a finite non-soluble group with no `X`-injector. -/
def fittingClassWithoutInjectors : Prop :=
  ∃ X : GroupClass, IsFitting X ∧ (∃ (H : Type) (_ : Group H) (_ : Finite H), X.mem H) ∧
    ∃ (G : Type) (_ : Group G) (_ : Finite G), ¬ Group.IsSolvable G ∧
      ∀ V : Subgroup G, ¬ IsInjector X V

/--
Resolved true: the Kourovka Archive records that E. Salomon found such a Fitting class and group;
the example is presented in Section 7.1 of Ballester-Bolinches and Ezquerro, Classes of finite
groups (2006). Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory:
The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem
12.96 (L. A. Shemetkov); resolution: E. Salomon (unpublished), presented in A. Ballester-Bolinches
and L. M. Ezquerro, Classes of finite groups, Springer, 2006, Section 7.1, Kourovka Archive, Problem
12.96: found by E. Salomon.
-/
public theorem_wanted fittingClassWithoutInjectors_holds : fittingClassWithoutInjectors

end MathlibExt.GroupTheory.FittingClassWithoutInjectorKourovka12Problem96Wanted
