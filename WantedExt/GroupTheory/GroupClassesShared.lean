/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Shared group classes for Kourovka Notebook WantedExt statements

Definitions used by more than one `WantedExt` module of resolved Kourovka Notebook problems:
generalized quaternion groups (Problems 4.75, 7.15). Mathlib and MathlibExt have no such predicate
(checked 2026-10-23; Mathlib's `QuaternionGroup n` is the group itself, not a predicate). Fully
invariant subgroups, which describe varieties of groups through their laws (Problems 6.14-6.17,
7.24, 8.18, 8.22, 8.26), use `IsFullyInvariant` of the Kourovka 3.53 entry; conjugacy separable
groups (Problems 8.69, 8.70, 8.71, 9.2) use `IsConjugacySeparable` of `KourovkaNotebookShared`.
Locally finite groups use `IsLocallyFinite` below and locally normal groups (Problems 6.8, 6.9)
use `IsLocallyNormal`; Mathlib and MathlibExt have neither predicate (checked 2026-11-13).
Polycyclic and almost polycyclic groups (Problems 1.84, 2.16, 8.70, 11.5, 13.11) use
`IsPolycyclic` and `IsAlmostPolycyclic`, and Chernikov groups (Problems 1.81, 1.90, 4.36, 8.80,
11.116) use `IsChernikov`; Mathlib and MathlibExt have none of these predicates (checked
2026-11-13).
-/

module

public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.SpecificGroups.Quaternion

@[expose] public section

namespace MathlibExt.GroupTheory.GroupClassesShared

/-- `P` is a generalized quaternion group: `P ≅ Q_(2^(k+2))` (`QuaternionGroup (2 ^ k)`, of order
`2 ^ (k + 2) ≥ 8`) for some `k ≥ 1`. -/
def IsGeneralizedQuaternion (P : Type*) [Group P] : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ Nonempty (P ≃* QuaternionGroup (2 ^ k))

/-- `G` is locally finite: every finitely generated subgroup is finite. -/
def IsLocallyFinite (G : Type*) [Group G] : Prop :=
  ∀ s : Finset G, Finite (Subgroup.closure (s : Set G))

/-- `G` is locally normal: every finite subset lies in a finite normal subgroup. -/
def IsLocallyNormal (G : Type*) [Group G] : Prop :=
  ∀ S : Finset G, ∃ N : Subgroup G, N.Normal ∧ (N : Set G).Finite ∧ (S : Set G) ⊆ N

/-- `G` is polycyclic: it has a finite subnormal series `1 = H₀ ≤ H₁ ≤ ⋯ ≤ Hₙ = G`, each `Hᵢ`
normal in `Hᵢ₊₁`, with cyclic factors `Hᵢ₊₁ / Hᵢ`. By Hirsch's theorem these are exactly the soluble
groups all of whose subgroups are finitely generated. -/
def IsPolycyclic (G : Type*) [Group G] : Prop :=
  ∃ (n : ℕ) (H : Fin (n + 1) → Subgroup G), H 0 = ⊥ ∧ H (Fin.last n) = ⊤ ∧
    ∀ i : Fin n, H i.castSucc ≤ H i.succ ∧
      ∃ _ : ((H i.castSucc).subgroupOf (H i.succ)).Normal,
        IsCyclic (H i.succ ⧸ (H i.castSucc).subgroupOf (H i.succ))

/-- `G` is almost polycyclic (polycyclic-by-finite, virtually polycyclic): some subgroup of finite
index is polycyclic. -/
def IsAlmostPolycyclic (G : Type*) [Group G] : Prop :=
  ∃ H : Subgroup G, H.FiniteIndex ∧ IsPolycyclic H

/-- `G` is a Chernikov group: it has an abelian subgroup of finite index satisfying the minimal
condition on subgroups. An abelian group with the minimal condition is a direct product of finitely
many quasicyclic groups and a finite group, so this is the usual definition: a finite extension of
a direct product of finitely many quasicyclic groups (finite groups are the case of no factors). -/
def IsChernikov (G : Type*) [Group G] : Prop :=
  ∃ A : Subgroup G, A.FiniteIndex ∧ (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) ∧ WellFoundedLT (Subgroup A)

end MathlibExt.GroupTheory.GroupClassesShared
