/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Chvátal's hereditary intersecting-family conjecture
-/
module

public import Mathlib.Data.Finset.Card
public import MathlibExt.Combinatorics.SetFamily.UniformHypergraph
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Combinatorics.ChvatalHereditaryIntersectingWanted

/-! Source: Václav Chvátal's conjecture page
`https://users.encs.concordia.ca/~chvatal/conjecture.html` (also Erdős Problem 701). -/

/-- A family of sets is hereditary (an independence system) when it contains every
subset of each of its members. -/
def IsHereditary {α : Type*} (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, ∀ B : Finset α, B ⊆ A → B ∈ F

/-- Chvátal's conjecture: every nontrivial independence system (one containing a
nonempty set) has a point whose star is at least as large as every intersecting
subfamily. The point is fixed for the whole family, and the competing
subfamilies need not be hereditary. -/
def conjecture : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α] (F : Finset (Finset α)),
    IsHereditary F →
    (∃ A ∈ F, A.Nonempty) →
    ∃ x : α, ∀ G : Finset (Finset α),
      G ⊆ F → SetFamily.IsIntersecting G →
        G.card ≤ (F.filter (fun A => x ∈ A)).card

/--
Resolved true: Chang, Liu, and Liu (arXiv:2609.19123, 2026) prove Chvátal's conjecture: every
hereditary family of subsets of a finite set has a largest intersecting subfamily that is a
star. Ellis, Filmus, and Friedgut (arXiv:2609.28404) give an independent spectral proof, and
Keevash (arXiv:2609.23595) proves the stronger Kahn flow conjecture. erdosproblems.com/701 lists
the Chang–Liu–Liu proof claim with a Lean formalization by Boon Suan Ho. Source: Fan Chang, Hong
Liu, and Miao Liu, A proof of Chvátal's conjecture via a sharp correlation inequality,
arXiv:2609.19123 (2026), https://arxiv.org/abs/2609.19123; David Ellis, Yuval Filmus, and Ehud
Friedgut, Chvátal's conjecture: a proof from The Book, arXiv:2609.28404v2 (2026),
https://arxiv.org/abs/2609.28404; Peter Keevash, On Kahn's flow conjecture, arXiv:2609.23595
(2026), https://arxiv.org/abs/2609.23595. Moved from
`OpenConjectures/Combinatorics/ChvatalHereditaryIntersecting`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.ChvatalHereditaryIntersectingWanted
