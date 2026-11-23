/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Products of two locally cyclic torsion-free groups (Kourovka Notebook Problem 2.70)

Kourovka Notebook, Archive of Solved Problems, Problem 2.70 (N. F. Sesekin): (a) let a group `G` be
the product of two subgroups `A` and `B`, each of which is locally cyclic and torsion-free. Prove
that either `A` or `B` has a non-trivial subgroup that is normal in `G`. (b) Characterize the groups
that can be factorized in this way.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.OrderOfElement

@[expose] public section

namespace MathlibExt.GroupTheory.ProductLocallyCyclicTorsionFreeKourovka2Problem70Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 2.70 (N. F.
Sesekin). UnsolvedMath record UM-00700140 (`KOU-2.70`), dataset ulamai/UnsolvedMath v1.8.0.

`G` is required to be nontrivial: for `A = B = 1` there is no non-trivial subgroup at all. Locally
cyclic means any two elements lie in a common cyclic subgroup; torsion-free means non-identity
elements have infinite order. Part (b), the characterization (Sysak, 1986), is not formalized.
-/

/-- A subgroup is locally cyclic: any two of its elements lie in a common cyclic subgroup (so
every finitely generated subgroup is cyclic). -/
def IsLocallyCyclicSubgroup {G : Type} [Group G] (A : Subgroup G) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∃ z ∈ A, x ∈ Subgroup.zpowers z ∧ y ∈ Subgroup.zpowers z

/-- A subgroup is torsion-free: its non-identity elements have infinite order. -/
def IsTorsionFreeSubgroup {G : Type} [Group G] (A : Subgroup G) : Prop :=
  ∀ a ∈ A, a ≠ 1 → ¬ IsOfFinOrder a

/-- Kourovka 2.70(a) (N. F. Sesekin): if a nontrivial group `G = AB` is the product of two locally
cyclic torsion-free subgroups `A` and `B`, then `A` or `B` contains a non-trivial subgroup that is
normal in `G`. -/
def productLocallyCyclicHasNormalSubgroup : Prop :=
  ∀ (G : Type) [Group G] [Nontrivial G] (A B : Subgroup G),
    IsLocallyCyclicSubgroup A → IsTorsionFreeSubgroup A →
    IsLocallyCyclicSubgroup B → IsTorsionFreeSubgroup B →
    (∀ g : G, ∃ a ∈ A, ∃ b ∈ B, g = a * b) →
      ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ (N ≤ A ∨ N ≤ B)

/--
Resolved true: the Kourovka Archive records that 2.70(a) was proved by Zaitsev (1980). Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 2.70 (N. F. Sesekin);
resolution: D. I. Zaitsev, Algebra and Logic 19 (1980), 94-106; Ya. P. Sysak, Algebra and Logic 25
(1986), 425-433, Kourovka Archive, Problem 2.70: a) this was proved (Zaitsev); b) they were
characterized (Sysak), https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted productLocallyCyclicHasNormalSubgroup_holds :
    productLocallyCyclicHasNormalSubgroup

end MathlibExt.GroupTheory.ProductLocallyCyclicTorsionFreeKourovka2Problem70Wanted
