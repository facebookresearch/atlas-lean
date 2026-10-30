/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Periodic subgroups inside a product of periodic subgroups (Kourovka Notebook Problem 16.38)

Kourovka Notebook, Problem 16.38 (F. de Giovanni): let `G` be a soluble group, and let `A` and `B`
be periodic subgroups of `G`. Is it true that any subgroup of `G` contained in the set `AB = {ab | a
∈ A, b ∈ B}` is periodic? (Known if `AB` is a subgroup.)
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Solvable

@[expose] public section

namespace MathlibExt.GroupTheory.PeriodicSubgroupsInProductSetKourovka16Problem38Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 16.38 (F. de Giovanni). UnsolvedMath record
UM-00701230 (`KOU-16.38`), dataset ulamai/UnsolvedMath v1.8.0.

Soluble is `Group.IsSolvable` (finite derived length), periodic means that every element has finite
order, and `AB` is the pointwise product of the underlying sets; `G` may be infinite.
-/

open Pointwise

/-- Kourovka 16.38 (F. de Giovanni): if `A` and `B` are periodic subgroups of a soluble group `G`,
then every subgroup of `G` contained in the set `AB = {a b | a ∈ A, b ∈ B}` is periodic. -/
def subgroupInPeriodicProductIsPeriodic : Prop :=
  ∀ (G : Type) [Group G], Group.IsSolvable G → ∀ A B : Subgroup G,
    (∀ a ∈ A, IsOfFinOrder a) → (∀ b ∈ B, IsOfFinOrder b) →
    ∀ H : Subgroup G, (H : Set G) ⊆ (A : Set G) * (B : Set G) → ∀ h ∈ H, IsOfFinOrder h

/--
Resolved true: Kinyon and Urban (Proposition 3.8) prove that if `G` is soluble and `A, B ≤ G` are
periodic, every subgroup contained in the set `AB` is periodic; the Kourovka Notebook (21st issue)
answers 16.38 "Yes, it is true", with the AI-generated solution confirmed by B. Amberg. Source: E.
I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Problem 16.38 (F. de Giovanni); resolution: M. Kinyon and J. Urban
(with Codex gpt-6-astra), Results on problems from the Kourovka Notebook, preprint, version 4 (19
September 2026), Proposition 3.8 (if G is soluble and A, B ≤ G are periodic, every subgroup
contained in the set AB is periodic); the Kourovka Notebook (21st issue) marks 16.38 solved (Yes, AI
solution confirmed by B. Amberg),
https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/09/kourovka-mathematics.pdf.
-/
public theorem_wanted subgroupInPeriodicProductIsPeriodic_holds :
    subgroupInPeriodicProductIsPeriodic

end MathlibExt.GroupTheory.PeriodicSubgroupsInProductSetKourovka16Problem38Wanted
