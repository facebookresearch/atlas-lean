/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Finset.Card

/-!
# Brambles

Two vertex sets of a graph touch if they share a vertex or some edge joins them. A bramble is a
set of mutually touching connected vertex sets; a cover of a bramble is a vertex set meeting every
member, and the order of a bramble is the least size of a cover. Brambles are the obstruction
to small tree-width in the tree-width duality theorem of Seymour and Thomas (Diestel,
*Graph Theory*, 6th ed., Theorem 12.4.3).

We record "order greater than `k`" as the predicate `SimpleGraph.IsBramble.OrderGT`: no set of
at most `k` vertices covers the bramble.

## References

* R. Diestel, *Graph Theory*, 6th edition, Chapter 12 (author's online preview of Chapter 12,
  PDF dated 28 June 2024, https://diestel-graph-theory.com/), Section 12.4.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- **Touching vertex sets.** Two vertex sets `X, Y` of `G` touch if they have a vertex in common
or `G` contains an edge between them (Diestel, *Graph Theory*, 6th ed., Section 12.4). -/
def Touch (X Y : Set V) : Prop :=
  (X ∩ Y).Nonempty ∨ ∃ x ∈ X, ∃ y ∈ Y, G.Adj x y

/-- **Bramble.** A set `B` of vertex sets of `G` is a bramble if every member induces a connected
(in particular nonempty) subgraph and any two members touch (Diestel, *Graph Theory*, 6th ed.,
Section 12.4). -/
def IsBramble (B : Set (Set V)) : Prop :=
  (∀ X ∈ B, (G.induce X).Connected) ∧ ∀ X ∈ B, ∀ Y ∈ B, G.Touch X Y

/-- **Bramble of order greater than `k`.** A bramble `B` has order greater than `k` if no set of
at most `k` vertices meets every member of `B`; the order of `B` is the least size of a vertex
set meeting every member (Diestel, *Graph Theory*, 6th ed., Section 12.4). -/
def IsBramble.OrderGT {G : SimpleGraph V} {B : Set (Set V)} (_ : G.IsBramble B) (k : ℕ) : Prop :=
  ∀ S : Finset V, S.card ≤ k → ∃ X ∈ B, ∀ x ∈ X, x ∉ S

/-- **Touching is symmetric.** -/
theorem Touch.symm {G : SimpleGraph V} {X Y : Set V} (h : G.Touch X Y) : G.Touch Y X := by
  rcases h with ⟨x, hxX, hxY⟩ | ⟨x, hx, y, hy, hxy⟩
  · exact Or.inl ⟨x, hxY, hxX⟩
  · exact Or.inr ⟨y, hy, x, hx, hxy.symm⟩

/-- **Small graphs have no large brambles.** In a graph with at most `k` vertices, every bramble is
covered by the whole vertex set, so no bramble has order greater than `k`. -/
theorem IsBramble.not_orderGT_of_card_le [Fintype V] {B : Set (Set V)} (hB : G.IsBramble B)
    {k : ℕ} (hV : Fintype.card V ≤ k) : ¬hB.OrderGT k := by
  intro h
  obtain ⟨X, hX, hXS⟩ := h Finset.univ (by simpa using hV)
  obtain ⟨⟨x, hx⟩⟩ := (hB.1 X hX).nonempty
  exact hXS x hx (Finset.mem_univ x)

end SimpleGraph
