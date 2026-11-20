/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKRectMedialToggle

open SimpleGraph

namespace StatMech.FrontierD

def fkMedialWestDart (v : T.Vertex) : FKMedialDart T := (v, .west)
def fkMedialEastDart (v : T.Vertex) : FKMedialDart T := (v, .east)


def fkMedialOldLocalEdges (pairing : FKMedialLoopPairing T) (v : T.Vertex) :
    Set (Sym2 (FKMedialDart T)) :=
  {s(fkMedialWestDart v,
      fkMedialLocalMate pairing (fkMedialWestDart v)),
    s(fkMedialEastDart v,
      fkMedialLocalMate pairing (fkMedialEastDart v))}


def fkMedialNewLocalEdges (pairing : FKMedialLoopPairing T) (v : T.Vertex) :
    Set (Sym2 (FKMedialDart T)) :=
  {s(fkMedialWestDart v,
      fkMedialLocalMate (fkMedialTogglePairingAt pairing v)
        (fkMedialWestDart v)),
    s(fkMedialEastDart v,
      fkMedialLocalMate (fkMedialTogglePairingAt pairing v)
        (fkMedialEastDart v))}

set_option maxHeartbeats 800000 in



theorem fkMedialLoopGraph_toggle_eq (T : EvenTorus)
    (pairing : FKMedialLoopPairing T) (v : T.Vertex) :
    fkMedialLoopGraph T (fkMedialTogglePairingAt pairing v) =
      (fkMedialLoopGraph T pairing).deleteEdges
          (fkMedialOldLocalEdges pairing v) ⊔
        fromEdgeSet (fkMedialNewLocalEdges pairing v) := by
  ext d e
  rcases d with ⟨dv, ds⟩
  rcases e with ⟨ev, es⟩
  by_cases hd : dv = v <;> by_cases he : ev = v
  · subst dv
    subst ev
    cases hp : pairing v <;> cases ds <;> cases es <;>
      simp [fkMedialLoopGraph_adj_iff, fkMedialOldLocalEdges,
        fkMedialNewLocalEdges, fkMedialWestDart, fkMedialEastDart,
        fkMedialLocalMate, fkMedialBondMate, fkMedialTogglePairingAt, hp,
        SimpleGraph.deleteEdges_adj, SimpleGraph.sup_adj,
        SimpleGraph.fromEdgeSet_adj]
  · subst dv
    cases hp : pairing v <;> cases ds <;> cases es <;>
      simp [fkMedialLoopGraph_adj_iff, fkMedialOldLocalEdges,
        fkMedialNewLocalEdges, fkMedialWestDart, fkMedialEastDart,
        fkMedialLocalMate, fkMedialBondMate, fkMedialTogglePairingAt, hp, he,
        SimpleGraph.deleteEdges_adj, SimpleGraph.sup_adj,
        SimpleGraph.fromEdgeSet_adj]
  · subst ev
    cases hp : pairing v <;> cases ds <;> cases es <;>
      simp [fkMedialLoopGraph_adj_iff, fkMedialOldLocalEdges,
        fkMedialNewLocalEdges, fkMedialWestDart, fkMedialEastDart,
        fkMedialLocalMate, fkMedialBondMate, fkMedialTogglePairingAt, hp, hd,
        SimpleGraph.deleteEdges_adj, SimpleGraph.sup_adj,
        SimpleGraph.fromEdgeSet_adj]
  · cases hpd : pairing dv <;> cases hpe : pairing ev <;>
      cases ds <;> cases es <;>
      simp [fkMedialLoopGraph_adj_iff, fkMedialOldLocalEdges,
        fkMedialNewLocalEdges, fkMedialWestDart, fkMedialEastDart,
        fkMedialLocalMate, fkMedialBondMate, fkMedialTogglePairingAt, hpd, hd, he,
        SimpleGraph.deleteEdges_adj, SimpleGraph.sup_adj,
        SimpleGraph.fromEdgeSet_adj]

end StatMech.FrontierD
