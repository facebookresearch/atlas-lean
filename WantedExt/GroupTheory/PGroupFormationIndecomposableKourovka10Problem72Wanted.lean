/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Indecomposability of the formation of finite `p`-groups (Kourovka Notebook Problem 10.72)

Kourovka Notebook, Archive of Solved Problems, Problem 10.72 (L. A. Shemetkov): prove that the
formation of all finite `p`-groups does not decompose into a product of two non-trivial
subformations.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.PUnit
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.PGroup

@[expose] public section

namespace MathlibExt.GroupTheory.PGroupFormationIndecomposableKourovka10Problem72Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 10.72 (L. A.
Shemetkov). UnsolvedMath record UM-00700687 (`KOU-10.72`), dataset ulamai/UnsolvedMath v1.8.0.

A formation is an isomorphism-closed class of finite groups (in `Type`) that contains the trivial
group and is closed under quotients and subdirect products; the product is Gaschütz's `𝔉 ∘ 𝔊` (`G ∈
𝔉 ∘ 𝔊` iff the `𝔊`-residual of `G` lies in `𝔉`). Non-trivial subformations are read as subformations
of `𝔑_p` different from the formation of trivial groups and from `𝔑_p` itself: `𝔑_p ∘ 𝔊 = 𝔉 ∘ 𝔑_p =
𝔑_p` for all subformations `𝔉, 𝔊` of `𝔑_p`, so admitting the factor `𝔑_p` would make the statement
false.
-/

/-- A class of finite groups, given by its membership predicate. -/
abbrev GroupClass : Type 1 :=
  ∀ (G : Type) [Group G] [Finite G], Prop

/-- A formation of finite groups: an isomorphism-closed class of finite groups that contains the
trivial group and is closed under quotients and subdirect products. -/
def IsFormation (X : GroupClass) : Prop :=
  (∀ (G H : Type) [Group G] [Finite G] [Group H] [Finite H], (G ≃* H) → X G → X H) ∧ X Unit ∧
  (∀ (G : Type) [Group G] [Finite G] (N : Subgroup G) [N.Normal], X G → X (G ⧸ N)) ∧
  ∀ (G : Type) [Group G] [Finite G] (N₁ N₂ : Subgroup G) [N₁.Normal] [N₂.Normal],
    X (G ⧸ N₁) → X (G ⧸ N₂) → X (G ⧸ (N₁ ⊓ N₂))

/-- The `X`-residual of a finite group `G`: the intersection of the normal subgroups `N` with
`G / N ∈ X` (for a formation, the smallest such `N`). -/
def residual (X : GroupClass) (G : Type) [Group G] [Finite G] : Subgroup G :=
  ⨅ (N : Subgroup G) (_ : ∃ _ : N.Normal, X (G ⧸ N)), N

/-- Kourovka 10.72 (L. A. Shemetkov): the formation `𝔑_p` of all finite `p`-groups is not the
Gaschütz product `𝔉 ∘ 𝔊` (`G ∈ 𝔉 ∘ 𝔊` iff the `𝔊`-residual of `G` lies in `𝔉`) of two non-trivial
proper subformations `𝔉, 𝔊`: each contains a nontrivial group and omits some finite `p`-group.
Properness is part of the reading: `𝔑_p ∘ 𝔊 = 𝔉 ∘ 𝔑_p = 𝔑_p` for all subformations `𝔉, 𝔊`. -/
def pGroupFormationIndecomposable : Prop :=
  ∀ p : ℕ, p.Prime → ∀ F H : GroupClass, IsFormation F → IsFormation H →
    (∀ (G : Type) [Group G] [Finite G], F G → IsPGroup p G) →
    (∀ (G : Type) [Group G] [Finite G], H G → IsPGroup p G) →
    (∃ (G : Type) (_ : Group G) (_ : Finite G), Nontrivial G ∧ F G) →
    (∃ (G : Type) (_ : Group G) (_ : Finite G), Nontrivial G ∧ H G) →
    (∃ (G : Type) (_ : Group G) (_ : Finite G), IsPGroup p G ∧ ¬ F G) →
    (∃ (G : Type) (_ : Group G) (_ : Finite G), IsPGroup p G ∧ ¬ H G) →
    ¬ ∀ (G : Type) [Group G] [Finite G], IsPGroup p G ↔ F (residual H G)

/--
Resolved true: the Kourovka Archive records "This has been proved", citing Skiba and Shemetkov
(1989): the formation `𝔑_p` of finite `p`-groups is not the product of two non-trivial proper
subformations. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory:
The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem
10.72 (L. A. Shemetkov); resolution: A. N. Skiba and L. A. Shemetkov, Dokl. Akad. Nauk BSSR 33
(1989), 581-582 (Russian), Kourovka Archive, Problem 10.72 ("This has been proved").
-/
public theorem_wanted pGroupFormationIndecomposable_holds : pGroupFormationIndecomposable

end MathlibExt.GroupTheory.PGroupFormationIndecomposableKourovka10Problem72Wanted
