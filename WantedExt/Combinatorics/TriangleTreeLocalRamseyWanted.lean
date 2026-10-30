/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Ramsey hosts locally given by trees of triangles

`AIM-COMBINATORICS-0056` (AIM Graph Ramsey theory, Local trees of
triangles, Rodl): for every `ℓ`, does there exist `G →₂ K₃` which on
every `ℓ` vertices induces a subgraph of a tree of triangles?
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Fintype.Basic
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Combinatorics.TriangleTreeLocalRamseyWanted

/-- Tree of triangles (recursive construction).

Source: AIM-COMBINATORICS-0056, aim-combinatorics-notes.json notes[55]:
any graph built recursively by starting with a triangle, and then adding two
edges at a time that forms a single new triangle with an existing edge. -/
inductive IsTriangleTree {V : Type*} : SimpleGraph V → Prop where
  | base : ∀ (H : SimpleGraph V) (a b c : V),
      a ≠ b → b ≠ c → a ≠ c →
      H.Adj a b → H.Adj b c → H.Adj a c →
      (∀ x y : V, H.Adj x y →
        (x = a ∨ x = b ∨ x = c) ∧ (y = a ∨ y = b ∨ y = c)) →
      (∀ x y : V, (x = a ∨ x = b ∨ x = c) →
        (y = a ∨ y = b ∨ y = c) → x ≠ y → H.Adj x y) →
      IsTriangleTree H
  | step : ∀ (H₀ H : SimpleGraph V) (z x y : V),
      IsTriangleTree H₀ →
      H₀.Adj x y → x ≠ y → z ≠ x → z ≠ y →
      (¬ ∃ w : V, H₀.Adj z w) →
      H.Adj x z → H.Adj y z →
      (∀ w : V, H.Adj z w → w = x ∨ w = y) →
      (∀ u v : V, u ≠ z → v ≠ z → (H.Adj u v ↔ H₀.Adj u v)) →
      IsTriangleTree H

/-- Two-color Ramsey arrow to the triangle: `G →₂ K₃`.

Source: AIM-COMBINATORICS-0056, aim-combinatorics-notes.json notes[55]:
`G` with `2` colors arrows `K₃`, i.e. every 2-coloring of the edges of `G`
contains a monochromatic triangle. -/
def Ramseys2Triangle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ χ : ∀ (x y : V), G.Adj x y → Fin 2,
    (∀ (x y : V) (h₁ : G.Adj x y) (h₂ : G.Adj y x), χ x y h₁ = χ y x h₂) →
    ∃ a b c : V, ∃ (hab : G.Adj a b) (hbc : G.Adj b c) (hac : G.Adj a c),
      a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ χ a b hab = χ b c hbc ∧ χ a b hab = χ a c hac

/-- Locally a tree of triangles on `ℓ` vertices.

Source: AIM-COMBINATORICS-0056, aim-combinatorics-notes.json notes[55]:
on every `ℓ` vertices `G` induces a subgraph of a tree of triangles. -/
@[nolint unusedArguments]
def IsLocallyTriangleTree {V : Type*} [DecidableEq V] (G : SimpleGraph V) (ℓ : ℕ) : Prop :=
  ∀ S : Finset V, S.card = ℓ →
    ∃ H' : SimpleGraph V, IsTriangleTree H' ∧
      ∀ x y : V, x ∈ S → y ∈ S → G.Adj x y → H'.Adj x y

/-- Formerly open, resolved true (`conjecture_holds` below): for every `ℓ` there is `G →₂ K₃`
locally a tree of triangles.

Source: AIM-COMBINATORICS-0056, aim-combinatorics-notes.json notes[55]:
for every `ℓ`, does there exist a graph `G →₂ K₃` which on every `ℓ` vertices
induces a subgraph of a tree of triangles. -/
def conjecture : Prop :=
  ∀ ℓ : ℕ, ∃ (V : Type), ∃ (_ : DecidableEq V), ∃ (_ : Fintype V),
    ∃ G : SimpleGraph V, ℓ ≤ Fintype.card V ∧ Ramseys2Triangle G ∧ IsLocallyTriangleTree G ℓ

/--
Resolved true: Resolved true: Reiher and Rödl's girth Ramsey theorem (arXiv:2308.15589, Theorem
1.6 with F = K_3, r = 2, n = l) gives a graph H -> (K_3)_2 in which every set of at most l
vertices induces a partial K_3-forest; such graphs have treewidth at most 2, hence lie in trees
of triangles (2-trees). Source: C. Reiher and V. Rödl, The girth Ramsey theorem,
arXiv:2308.15589, https://arxiv.org/abs/2308.15589. Moved from
`OpenConjectures/Combinatorics/TriangleTreeLocalRamsey`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.TriangleTreeLocalRamseyWanted
