/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Products of two abelian minimax groups (Kourovka Notebook Problem 4.57)

Kourovka Notebook, Archive of Solved Problems, Problem 4.57 (N. F. Sesekin): let a group `G` be the
product of two of its abelian minimax subgroups `A` and `B`. Prove or refute the following
statements: a) `A₀B₀ ≠ 1`, where `A₀ = ⋂_{x ∈ G} Aˣ` and similarly for `B₀`; b) the derived subgroup
of `G` is a minimax subgroup.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.ProductAbelianMinimaxKourovka4Problem57Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 4.57 (N. F.
Sesekin). UnsolvedMath record UM-00700264 (`KOU-4.57`), dataset ulamai/UnsolvedMath v1.8.0.

`G = AB` means every element is a product `ab`. A minimax group has a finite series, each term
normal in the next, whose factors satisfy the maximal or the minimal condition on subgroups; a
factor `Hᵢ₊₁ / Hᵢ` satisfies the maximal (minimal) condition exactly when the interval `[Hᵢ, Hᵢ₊₁]`
of the subgroup lattice has no infinite ascending (descending) chain. `A₀`, `B₀` are the normal
cores (`Subgroup.normalCore`) and `A₀B₀ ≠ 1` is `A₀ ⊔ B₀ ≠ ⊥`. In a) `G` is non-trivial, since for
`G = 1` the product `A₀B₀` is trivial.
-/

/-- The subgroup `K` of `G` is minimax: it has a finite series `⊥ = H₀ ≤ H₁ ≤ ⋯ ≤ Hₙ = K`, each
term normal in the next, whose factors satisfy the maximal or the minimal condition on subgroups.
A factor `Hᵢ₊₁ / Hᵢ` satisfies the maximal (minimal) condition exactly when the interval
`[Hᵢ, Hᵢ₊₁]` of the subgroup lattice has no infinite ascending (descending) chain. -/
def IsMinimax {G : Type*} [Group G] (K : Subgroup G) : Prop :=
  ∃ (n : ℕ) (H : ℕ → Subgroup G), H 0 = ⊥ ∧ H n = K ∧
    ∀ i < n, H i ≤ H (i + 1) ∧ ((H i).subgroupOf (H (i + 1))).Normal ∧
      (WellFoundedGT (Set.Icc (H i) (H (i + 1))) ∨ WellFoundedLT (Set.Icc (H i) (H (i + 1))))

/-- `G = AB` is the product of its subgroups `A` and `B`, with `A`, `B` abelian and minimax. -/
def IsProductOfAbelianMinimax {G : Type*} [Group G] (A B : Subgroup G) : Prop :=
  (∀ g : G, ∃ a ∈ A, ∃ b ∈ B, g = a * b) ∧ (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) ∧
    (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) ∧ IsMinimax A ∧ IsMinimax B

/-- Kourovka 4.57(a) (N. F. Sesekin): if a non-trivial group `G = AB` is the product of two
abelian minimax subgroups, then `A₀B₀ ≠ 1`, where `A₀ = ⋂_{x ∈ G} Aˣ` and `B₀` are the normal
cores. -/
def productAbelianMinimaxCoreNontrivial : Prop :=
  ∀ (G : Type) [Group G] [Nontrivial G] (A B : Subgroup G), IsProductOfAbelianMinimax A B →
    A.normalCore ⊔ B.normalCore ≠ ⊥

/-- Kourovka 4.57(b) (N. F. Sesekin): if a group `G = AB` is the product of two abelian minimax
subgroups, then the derived subgroup of `G` is minimax. -/
def productAbelianMinimaxDerivedMinimax : Prop :=
  ∀ (G : Type) [Group G] (A B : Subgroup G), IsProductOfAbelianMinimax A B →
    IsMinimax (commutator G)

/--
Resolved true: Zaitsev proves that if a non-trivial group `G = AB` is the product of two abelian
minimax subgroups, then `A₀B₀ ≠ 1`; the Kourovka Archive records that both parts of 4.57 were
proved. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 4.57
(N. F. Sesekin); resolution: D. I. Zaitsev, Products of abelian groups, Algebra and Logic 19 (1980),
94-106, Kourovka Archive of Solved Problems, Problem 4.57: Both parts were proved,
https://doi.org/10.1007/BF01669835.
-/
public theorem_wanted productAbelianMinimaxCoreNontrivial_holds :
    productAbelianMinimaxCoreNontrivial

/--
Resolved true: Zaitsev proves that if a group `G = AB` is the product of two abelian minimax
subgroups, then the derived subgroup of `G` is minimax; the Kourovka Archive records that both parts
of 4.57 were proved. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems,
Problem 4.57 (N. F. Sesekin); resolution: D. I. Zaitsev, Products of abelian groups, Algebra and
Logic 19 (1980), 94-106, Kourovka Archive of Solved Problems, Problem 4.57: Both parts were proved,
https://doi.org/10.1007/BF01669835.
-/
public theorem_wanted productAbelianMinimaxDerivedMinimax_holds :
    productAbelianMinimaxDerivedMinimax

end MathlibExt.GroupTheory.ProductAbelianMinimaxKourovka4Problem57Wanted
