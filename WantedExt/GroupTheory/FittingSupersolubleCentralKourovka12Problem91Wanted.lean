/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Fitting classes of supersoluble groups (Kourovka Notebook Problem 12.91)

Kourovka Notebook, Archive of Solved Problems, Problem 12.91 (H. Heineken): every metabelian group
belonging to a Fitting class of finite supersoluble groups is nilpotent. Does every group belonging
to a Fitting class of supersoluble groups have only central minimal normal subgroups?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Finite.Defs
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.FittingSupersolubleCentralKourovka12Problem91Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.91 (H.
Heineken). UnsolvedMath record UM-00700908 (`KOU-12.91`), dataset ulamai/UnsolvedMath v1.8.0.

Classes of finite groups are isomorphism-closed predicates on groups in `Type` (`GroupClass`, as in
the `OpenConjectures` entries `Kourovka11Problem117` and `Kourovka12Problem35`); only their finite
members are constrained. A Fitting class is closed under normal subgroups and under products of two
normal members. Supersoluble means a series of normal subgroups with cyclic factors; a minimal
normal subgroup is a nontrivial normal subgroup containing no smaller nontrivial normal subgroup.
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

/-- `G` is supersoluble: it has a series `⊥ = s 0 ≤ ⋯ ≤ s k = ⊤` of normal subgroups of `G` with
cyclic factors (`s (i + 1) = ⟨x⟩ ⊔ s i`). -/
def IsSupersoluble (G : Type*) [Group G] : Prop :=
  ∃ (k : ℕ) (s : ℕ → Subgroup G), s 0 = ⊥ ∧ s k = ⊤ ∧ ∀ i < k, s i ≤ s (i + 1) ∧
    (s i).Normal ∧ ∃ x ∈ s (i + 1), s (i + 1) = Subgroup.closure {x} ⊔ s i

/-- `N` is a minimal normal subgroup of `G`. -/
def IsMinimalNormal {G : Type*} [Group G] (N : Subgroup G) : Prop :=
  N.Normal ∧ N ≠ ⊥ ∧ ∀ M : Subgroup G, M.Normal → M ≠ ⊥ → M ≤ N → M = N

/-- Kourovka 12.91 (H. Heineken): in every group belonging to a Fitting class of finite
supersoluble groups, every minimal normal subgroup is central. -/
def fittingSupersolubleMinimalNormalCentral : Prop :=
  ∀ X : GroupClass, IsFitting X →
    (∀ (G : Type) [Group G] [Finite G], X.mem G → IsSupersoluble G) →
    ∀ (G : Type) [Group G] [Finite G], X.mem G →
      ∀ N : Subgroup G, IsMinimalNormal N → N ≤ Subgroup.center G

/--
Resolved false: the Kourovka Archive answers 12.91 "No, it does not" (H. Heineken, 1997): some group
in a Fitting class of finite supersoluble groups has a non-central minimal normal subgroup. Source:
E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook,
21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.91 (H. Heineken);
resolution: H. Heineken, Rend. Sem. Mat. Univ. Padova 98 (1997), 241-251, Kourovka Archive, Problem
12.91: No, it does not.
-/
public theorem_wanted fittingSupersolubleMinimalNormalCentral_refuted :
    ¬ fittingSupersolubleMinimalNormalCentral

end MathlibExt.GroupTheory.FittingSupersolubleCentralKourovka12Problem91Wanted
