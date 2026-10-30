/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Mutually non-embedded groups with equal spectra (Kourovka Notebook Problem 16.106)

Kourovka Notebook, Archive of Solved Problems, Problem 16.106 (W. J. Shi): let `π_e(G)` denote the
set of orders of elements of `G` and `h(Γ)` the number of non-isomorphic finite groups `G` with
`π_e(G) = Γ`. Do there exist finite groups `G₁`, `G₂` such that `π_e(G₁) = π_e(G₂)`, `h(π_e(G₁)) <
∞`, and neither of them is isomorphic to a subgroup or a quotient of a normal subgroup of the other?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.OrderOfElement

@[expose] public section

namespace MathlibExt.GroupTheory.SameSpectrumIncomparableGroupsKourovka16Problem106Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.106 (W. J.
Shi). UnsolvedMath record UM-00701297 (`KOU-16.106`), dataset ulamai/UnsolvedMath v1.8.0.

`h(Γ) < ∞` is stated as a bound on the orders of the finite groups with spectrum `Γ`, which is
equivalent since there are finitely many groups of each order. A quotient of a normal subgroup of
`B` is the image of some `N ⊴ B` under a surjective homomorphism.
-/

/-- The spectrum `π_e(G)`: the set of orders of elements of `G`. -/
def elementOrders (G : Type*) [Group G] : Set ℕ :=
  Set.range (orderOf : G → ℕ)

/-- `A` is isomorphic to a subgroup of `B` or to a quotient of a normal subgroup of `B`. -/
def IsSubgroupOrNormalSectionOf (A B : Type*) [Group A] [Group B] : Prop :=
  (∃ f : A →* B, Function.Injective f) ∨
    ∃ N : Subgroup B, N.Normal ∧ ∃ f : N →* A, Function.Surjective f

/-- Kourovka 16.106 (W. J. Shi): there are finite groups `G₁`, `G₂` with `π_e(G₁) = π_e(G₂)`,
`h(π_e(G₁)) < ∞` (the finite groups with this spectrum have bounded order, so there are finitely
many up to isomorphism), and neither is isomorphic to a subgroup or to a quotient of a normal
subgroup of the other. -/
def sameSpectrumIncomparableGroups : Prop :=
  ∃ (G₁ G₂ : Type) (_ : Group G₁) (_ : Group G₂) (_ : Finite G₁) (_ : Finite G₂),
    elementOrders G₁ = elementOrders G₂ ∧
    (∃ B : ℕ, ∀ (G : Type) [Group G] [Finite G], elementOrders G = elementOrders G₁ →
      Nat.card G ≤ B) ∧
    ¬ IsSubgroupOrNormalSectionOf G₁ G₂ ∧ ¬ IsSubgroupOrNormalSectionOf G₂ G₁

/--
Resolved true: the Kourovka Archive answers 16.106 "Yes, there do", with the example `G₁ =
L₁₅(2⁶⁰).3` and `G₂ = L₁₅(2⁶⁰).5` (Grechkoseeva). Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Archive of Solved Problems, Problem 16.106 (W. J. Shi); resolution: M. A. Grechkoseeva, Algebra and
Logic 47 (2008), no. 4, 229-241, Kourovka Archive, Problem 16.106 (answer: Yes, there do, for
example G₁ = L₁₅(2⁶⁰).3 and G₂ = L₁₅(2⁶⁰).5).
-/
public theorem_wanted sameSpectrumIncomparableGroups_holds : sameSpectrumIncomparableGroups

end MathlibExt.GroupTheory.SameSpectrumIncomparableGroupsKourovka16Problem106Wanted
