/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Finite

/-! # Induced width of a vertex ordering -/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.GraphicalModels

variable {V : Type*} {n : ℕ}

/-- A fill step keeps all edges of the current graph and adds an edge between each pair
of distinct neighbours of `v` whose ranks under `order` are both lower than that of `v`. -/
def fillEarlierNeighbours (order : V ≃ Fin n) (G : SimpleGraph V) (v : V) : SimpleGraph V :=
  G ⊔ {
    Adj := fun x y => x ≠ y ∧ order x < order v ∧ order y < order v ∧ G.Adj v x ∧ G.Adj v y
    symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2.1, h.2.1, h.2.2.2.2, h.2.2.2.1⟩⟩
    loopless := ⟨fun _ h => h.1 rfl⟩ }

theorem fillEarlierNeighbours_adj (order : V ≃ Fin n) (G : SimpleGraph V) (v x y : V) :
    (fillEarlierNeighbours order G v).Adj x y ↔
      G.Adj x y ∨
        (x ≠ y ∧ order x < order v ∧ order y < order v ∧ G.Adj v x ∧ G.Adj v y) :=
  Iff.rfl

/-- The induced graph for ordering `order` fills from the highest rank to the lowest.
Each step uses the current graph, including fill edges already added, and never deletes edges.
Source: R. Dechter, *Bucket elimination: a unifying framework for reasoning*, §2.1. -/
def inducedGraph (order : V ≃ Fin n) (G : SimpleGraph V) : SimpleGraph V :=
  (List.finRange n).reverse.foldl (fun H i => fillEarlierNeighbours order H (order.symm i)) G

/-- All edges of the original graph are retained by the reverse fill process. -/
theorem le_inducedGraph (order : V ≃ Fin n) (G : SimpleGraph V) : G ≤ inducedGraph order G := by
  have h (ks : List (Fin n)) (H : SimpleGraph V) :
      H ≤ ks.foldl (fun J i => fillEarlierNeighbours order J (order.symm i)) H := by
    induction ks generalizing H with
    | nil => exact le_rfl
    | cons k ks ih =>
      exact le_trans le_sup_left (ih (fillEarlierNeighbours order H (order.symm k)))
  exact h _ G

/-- **Induced width of an ordering.** The maximum number of earlier neighbours of any vertex
in the induced graph. The maximum is zero on the empty vertex type. This definition concerns a
fixed ordering, not the minimum over orderings or its relation to tree-width.
Source: R. Dechter, *Bucket elimination: a unifying framework for reasoning*, §2.1. -/
noncomputable def inducedWidth [Fintype V] (order : V ≃ Fin n) (G : SimpleGraph V) : ℕ := by
  classical
  exact Finset.univ.sup fun v =>
    (Finset.univ.filter fun u => order u < order v ∧ (inducedGraph order G).Adj v u).card

end Cslib.MachineLearning.GraphicalModels
