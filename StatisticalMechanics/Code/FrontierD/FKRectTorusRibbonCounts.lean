/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.GenusOneRibbonEulerDefect
import Code.FrontierD.FKRectTorusMedial

namespace StatMech.FrontierD


theorem fkRectTorus_card_vertex (R : FKRectTorus) :
    Fintype.card R.Vertex = R.width * R.height := by
  simp [FKRectTorus.Vertex]


theorem fkRectTorus_card_edgeIndex (R : FKRectTorus) :
    Fintype.card R.EdgeIndex = 2 * R.width * R.height := by
  simp [FKRectTorus.EdgeIndex]
  ring



def fkRectTorusCellularFaceCount (R : FKRectTorus) : Nat :=
  R.width * R.height



theorem fkRectTorus_cellularEuler_genus_one (R : FKRectTorus) :
    Fintype.card R.Vertex + fkRectTorusCellularFaceCount R + 2 * 1 =
      Fintype.card R.EdgeIndex + 2 := by
  rw [fkRectTorus_card_vertex, fkRectTorus_card_edgeIndex]
  unfold fkRectTorusCellularFaceCount
  ring


theorem fkRectTorus_vertex_eq_faceCount (R : FKRectTorus) :
    Fintype.card R.Vertex = fkRectTorusCellularFaceCount R := by
  rw [fkRectTorus_card_vertex]
  rfl

end StatMech.FrontierD
