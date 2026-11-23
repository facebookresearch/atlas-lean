/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# The cyclomatic number of a connected finite graph

For a connected finite graph, `|E| + 1 ≥ |V|`, with equality exactly for trees. The cyclomatic
number `|E| + 1 - |V|` therefore vanishes exactly on trees and is positive exactly when the graph
has a cycle.

## Main definitions

* `StatMech.Lattice.cyclomaticNumber G`: the cyclomatic number (first Betti number) of a connected
  graph.

## Main results

* `StatMech.Lattice.connected_card_edges_ge`: a connected graph has at least `|V| - 1` edges; see
  also Mathlib's `SimpleGraph.Connected.card_vert_le_card_edgeSet_add_one`, of which this is the
  `Fintype` form.
* `StatMech.Lattice.connected_card_edges_eq_iff_isAcyclic`: equality holds exactly for acyclic
  graphs; see also `SimpleGraph.isTree_iff_connected_and_card`.
* `StatMech.Lattice.cyclomaticNumber_pos_iff_exists_cycle`: the cyclomatic number is positive iff
  the graph has a cycle.
-/

@[expose] public section

namespace StatMech.Lattice

open SimpleGraph

variable {V : Type*}

/-- A connected finite graph has at least `|V| - 1` edges. This is the `Fintype` form of Mathlib's
`SimpleGraph.Connected.card_vert_le_card_edgeSet_add_one`. -/
theorem connected_card_edges_ge {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    (hG : G.Connected) : Fintype.card V ≤ G.edgeFinset.card + 1 := by
  have h := hG.card_vert_le_card_edgeSet_add_one
  rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← edgeFinset_card] at h

/-- A connected finite graph has exactly `|V| - 1` edges iff it is acyclic. See also Mathlib's
`SimpleGraph.isTree_iff_connected_and_card` and `SimpleGraph.IsTree.card_edgeFinset`. -/
theorem connected_card_edges_eq_iff_isAcyclic {G : SimpleGraph V} [Fintype V]
    [Fintype G.edgeSet] (hG : G.Connected) :
    G.edgeFinset.card + 1 = Fintype.card V ↔ G.IsAcyclic := by
  constructor
  · intro h
    refine SimpleGraph.IsTree.isAcyclic ?_
    rw [isTree_iff_connected_and_card]
    refine ⟨hG, ?_⟩
    rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← edgeFinset_card]
  · intro hac
    exact (SimpleGraph.IsTree.card_edgeFinset ⟨hG, hac⟩)

theorem connected_isTree_iff_card_edges {G : SimpleGraph V} [Fintype V]
    [Fintype G.edgeSet] (hG : G.Connected) :
    G.IsTree ↔ G.edgeFinset.card + 1 = Fintype.card V := by
  rw [connected_card_edges_eq_iff_isAcyclic hG]
  exact ⟨fun h => h.isAcyclic, fun h => ⟨hG, h⟩⟩

theorem exists_spanning_tree_card {G : SimpleGraph V} [Finite V]
    (hG : G.Connected) :
    ∃ T : SimpleGraph V, T ≤ G ∧ T.IsTree ∧ Nat.card T.edgeSet + 1 = Nat.card V := by
  obtain ⟨T, hle, hT⟩ := hG.exists_isTree_le
  exact ⟨T, hle, hT, ((isTree_iff_connected_and_card).mp hT).2⟩

/-- The cyclomatic number `|E| + 1 - |V|` of a finite graph. For a connected graph it is the
dimension of the cycle space. See `StatMech.Lattice.nullity` for the version for arbitrary
finite graphs. -/
def cyclomaticNumber (G : SimpleGraph V) [Fintype V] [Fintype G.edgeSet] : ℕ :=
  (G.edgeFinset.card + 1) - Fintype.card V

theorem cyclomaticNumber_eq_zero_iff_isAcyclic {G : SimpleGraph V} [Fintype V]
    [Fintype G.edgeSet] (hG : G.Connected) :
    cyclomaticNumber G = 0 ↔ G.IsAcyclic := by
  unfold cyclomaticNumber
  rw [Nat.sub_eq_zero_iff_le]
  constructor
  · intro h
    have heq : G.edgeFinset.card + 1 = Fintype.card V :=
      le_antisymm h (connected_card_edges_ge hG)
    exact (connected_card_edges_eq_iff_isAcyclic hG).mp heq
  · intro hac
    rw [(connected_card_edges_eq_iff_isAcyclic hG).mpr hac]

theorem card_edges_eq_cyclomaticNumber_add {G : SimpleGraph V} [Fintype V]
    [Fintype G.edgeSet] (hG : G.Connected) :
    G.edgeFinset.card + 1 = Fintype.card V + cyclomaticNumber G := by
  have hge := connected_card_edges_ge hG
  unfold cyclomaticNumber
  omega

theorem not_isAcyclic_iff_exists_cycle {G : SimpleGraph V} :
    ¬ G.IsAcyclic ↔ ∃ (v : V) (c : G.Walk v v), c.IsCycle := by
  unfold SimpleGraph.IsAcyclic
  push Not
  rfl

theorem cyclomaticNumber_pos_iff_exists_cycle {G : SimpleGraph V} [Fintype V]
    [Fintype G.edgeSet] (hG : G.Connected) :
    0 < cyclomaticNumber G ↔ ∃ (v : V) (c : G.Walk v v), c.IsCycle := by
  rw [← not_isAcyclic_iff_exists_cycle, ← cyclomaticNumber_eq_zero_iff_isAcyclic hG,
    Nat.pos_iff_ne_zero]

end StatMech.Lattice
