/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.SpecificGroups.Quaternion

/-!
# Group classes in the Kourovka Notebook

This module defines generalized quaternion, locally finite, locally normal, polycyclic,
almost polycyclic and Chernikov groups.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.GroupClassesShared

/-- **Generalized quaternion group.** A group $P$ is a generalized quaternion group if, for some
natural number $k \ge 1$, it is isomorphic to the quaternion group
$Q_{2^{k+2}} = \langle a, x \mid a^{2^{k+1}} = 1,\ x^2 = a^{2^k},\ x^{-1} a x = a^{-1} \rangle$
of order $2^{k+2}$. Thus $P$ has order $8$, $16$, $32$ or some larger power of $2$. -/
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
