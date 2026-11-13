/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKMedialSwitchCount

open SimpleGraph Set

namespace StatMech.FrontierD

noncomputable section

private theorem fromEdgeSet_pair_eq_sup_edge {V : Type*} (a b c d : V) :
    fromEdgeSet {s(a, d), s(c, b)} = edge a d ⊔ edge c b := by
  ext x y
  simp only [fromEdgeSet_adj, Set.mem_insert_iff, Set.mem_singleton_iff,
    SimpleGraph.sup_adj, SimpleGraph.edge_adj]
  rw [Sym2.eq_iff, Sym2.eq_iff]
  tauto



theorem fkMedialNewLocalEdges_eq_crossed (pairing : FKMedialLoopPairing T)
    (v : T.Vertex) :
    fkMedialNewLocalEdges pairing v =
      {s(fkMedialWestDart v,
          fkMedialLocalMate pairing (fkMedialEastDart v)),
       s(fkMedialEastDart v,
          fkMedialLocalMate pairing (fkMedialWestDart v))} := by
  cases hp : pairing v <;>
    simp [fkMedialNewLocalEdges, fkMedialWestDart, fkMedialEastDart,
      fkMedialTogglePairingAt, fkMedialLocalMate, hp]



theorem fkMedialLoopCount_toggle_of_not_reachable
    (T : EvenTorus) (pairing : FKMedialLoopPairing T) (v : T.Vertex)
    (hdisc : ¬ (fkMedialLoopGraph T pairing).Reachable
      (fkMedialWestDart v) (fkMedialEastDart v)) :
    fkMedialLoopCount T (fkMedialTogglePairingAt pairing v) + 1 =
      fkMedialLoopCount T pairing := by
  let G := fkMedialLoopGraph T pairing
  let a := fkMedialWestDart v
  let b := fkMedialLocalMate pairing (fkMedialWestDart v)
  let c := fkMedialEastDart v
  let d := fkMedialLocalMate pairing (fkMedialEastDart v)
  have hab : G.Adj a b := by
    rw [fkMedialLoopGraph_adj_iff]
    exact Or.inl rfl
  have hcd : G.Adj c d := by
    rw [fkMedialLoopGraph_adj_iff]
    exact Or.inl rfl
  have heven : ∀ x, Even (G.degree x) := by
    intro x
    rw [fkMedialLoopGraph_degree_eq_two]
    exact even_two
  have hcount := card_components_twoEdgeSwitch_of_not_reachable G heven
    hab hcd hdisc
  have hgraph :
      fkMedialLoopGraph T (fkMedialTogglePairingAt pairing v) =
        (G.deleteEdges {s(a, b), s(c, d)} ⊔ edge a d) ⊔ edge c b := by
    rw [fkMedialLoopGraph_toggle_eq,
      fkMedialNewLocalEdges_eq_crossed,
      fromEdgeSet_pair_eq_sup_edge]
    change G.deleteEdges {s(a, b), s(c, d)} ⊔ (edge a d ⊔ edge c b) =
      (G.deleteEdges {s(a, b), s(c, d)} ⊔ edge a d) ⊔ edge c b
    rw [sup_assoc]
  unfold fkMedialLoopCount
  change Nat.card
      (fkMedialLoopGraph T (fkMedialTogglePairingAt pairing v)).ConnectedComponent + 1 =
    Nat.card (fkMedialLoopGraph T pairing).ConnectedComponent
  rw [hgraph]
  exact hcount



theorem fkMedialLoopCount_toggle_le_add_one
    (T : EvenTorus) (pairing : FKMedialLoopPairing T) (v : T.Vertex) :
    fkMedialLoopCount T (fkMedialTogglePairingAt pairing v) ≤
      fkMedialLoopCount T pairing + 1 := by
  let G := fkMedialLoopGraph T pairing
  let a := fkMedialWestDart v
  let b := fkMedialLocalMate pairing (fkMedialWestDart v)
  let c := fkMedialEastDart v
  let d := fkMedialLocalMate pairing (fkMedialEastDart v)
  have hab : G.Adj a b := by
    rw [fkMedialLoopGraph_adj_iff]
    exact Or.inl rfl
  have heven : ∀ x, Even (G.degree x) := by
    intro x
    rw [fkMedialLoopGraph_degree_eq_two]
    exact even_two
  have hcount := card_components_twoEdgeSwitch_le_add_one G heven hab
      (c := c) (d := d)
  have hgraph :
      fkMedialLoopGraph T (fkMedialTogglePairingAt pairing v) =
        (G.deleteEdges {s(a, b), s(c, d)} ⊔ edge a d) ⊔ edge c b := by
    rw [fkMedialLoopGraph_toggle_eq,
      fkMedialNewLocalEdges_eq_crossed,
      fromEdgeSet_pair_eq_sup_edge]
    change G.deleteEdges {s(a, b), s(c, d)} ⊔ (edge a d ⊔ edge c b) =
      (G.deleteEdges {s(a, b), s(c, d)} ⊔ edge a d) ⊔ edge c b
    rw [sup_assoc]
  unfold fkMedialLoopCount
  change Nat.card
      (fkMedialLoopGraph T (fkMedialTogglePairingAt pairing v)).ConnectedComponent ≤
    Nat.card (fkMedialLoopGraph T pairing).ConnectedComponent + 1
  rw [hgraph]
  exact hcount

end

end StatMech.FrontierD
