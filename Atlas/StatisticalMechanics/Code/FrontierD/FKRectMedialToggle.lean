/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKRectTorusEdgeInsertion

open Finset

namespace StatMech.FrontierD



def fkMedialTogglePairingAt {T : EvenTorus}
    (pairing : FKMedialLoopPairing T) (v : T.Vertex) :
    FKMedialLoopPairing T :=
  fun w => if w = v then !pairing w else pairing w

@[simp] theorem fkMedialTogglePairingAt_self {T : EvenTorus}
    (pairing : FKMedialLoopPairing T) (v : T.Vertex) :
    fkMedialTogglePairingAt pairing v v = !pairing v := by
  simp [fkMedialTogglePairingAt]

theorem fkMedialTogglePairingAt_of_ne {T : EvenTorus}
    (pairing : FKMedialLoopPairing T) {v w : T.Vertex} (h : w ≠ v) :
    fkMedialTogglePairingAt pairing v w = pairing w := by
  simp [fkMedialTogglePairingAt, h]


def fkRectMedialVertexOfEdge (R : FKRectTorus) (e : R.EdgeIndex) :
    R.medialTorus.Vertex :=
  (fkRectTorusMedialEdgeEquiv R).symm e

@[simp] theorem fkRectTorusMedialEdgeEquiv_vertexOfEdge
    (R : FKRectTorus) (e : R.EdgeIndex) :
    fkRectTorusMedialEdgeEquiv R (fkRectMedialVertexOfEdge R e) = e := by
  simp [fkRectMedialVertexOfEdge]



theorem fkRectConfigurationToMedialPairing_insert
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (he : e ∉ F) :
    fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R (insert e F)) =
      fkMedialTogglePairingAt
        (fkRectConfigurationToMedialPairing R
          (fkRectConfigurationOfEdges R F))
        (fkRectMedialVertexOfEdge R e) := by
  funext w
  by_cases hw : w = fkRectMedialVertexOfEdge R e
  · subst w
    rw [fkMedialTogglePairingAt_self]
    simp only [fkRectConfigurationToMedialPairing_apply,
      fkRectTorusMedialEdgeEquiv_vertexOfEdge]
    have hnew : fkRectConfigurationOfEdges R (insert e F) e = true := by
      simp [fkRectConfigurationOfEdges]
    have hold : fkRectConfigurationOfEdges R F e = false := by
      simp [fkRectConfigurationOfEdges, he]
    rw [hnew, hold]
    cases fkRectClosedPairingAtEdge e <;> rfl
  · have hindex : fkRectTorusMedialEdgeEquiv R w ≠ e := by
      intro h
      apply hw
      exact (fkRectTorusMedialEdgeEquiv R).injective <| by
        rw [h, fkRectTorusMedialEdgeEquiv_vertexOfEdge]
    rw [fkMedialTogglePairingAt_of_ne _ hw]
    simp only [fkRectConfigurationToMedialPairing_apply]
    have hmem :
        (fkRectTorusMedialEdgeEquiv R w ∈ insert e F) ↔
          fkRectTorusMedialEdgeEquiv R w ∈ F := by
      simp [hindex]
    have hconfig :
        fkRectConfigurationOfEdges R (insert e F)
            (fkRectTorusMedialEdgeEquiv R w) =
          fkRectConfigurationOfEdges R F
            (fkRectTorusMedialEdgeEquiv R w) := by
      simp only [fkRectConfigurationOfEdges]
      rw [decide_eq_decide]
      exact hmem
    rw [hconfig]

end StatMech.FrontierD
