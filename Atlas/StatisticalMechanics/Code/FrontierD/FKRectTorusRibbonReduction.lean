/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKRectTorusConnected
import Code.FrontierD.FKRectTorusEulerDefect

open Finset

namespace StatMech.FrontierD

open StatMech.FrontierA

noncomputable section


theorem fkRectEulerHomologyDefect_configurationOfEdges
    (R : FKRectTorus) (F : Finset R.EdgeIndex) :
    fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R F) =
      2 * (fkRectFinsetClusterCount R F : Int) + (F.card : Int) -
        (fkRectMedialLoopCount R
          (fkRectConfigurationOfEdges R F) : Int) -
        (Fintype.card R.Vertex : Nat) := by
  unfold fkRectEulerHomologyDefect fkRectFinsetClusterCount
  rw [fkRectOpenEdgeCount_configurationOfEdges,
    fkRectTorus_card_vertex]








theorem fkRectEulerHomologyDefect_classified_of_ribbon
    (R : FKRectTorus) {D : Type*} [Fintype D] [DecidableEq D]
    (S : RibbonPermutationSystem R.EdgeIndex D)
    (C : CellularRibbonDualData S)
    (hprimal : C.primalVertexCount = Fintype.card R.Vertex)
    (hgenus : C.genus = 1)
    (hboundary : ∀ F : Finset R.EdgeIndex,
      S.boundaryComponents F =
        fkRectMedialLoopCount R (fkRectConfigurationOfEdges R F))
    (hfullBoundary :
      S.boundaryComponents Finset.univ = C.dualVertexCount)
    (hmono : ∀ (F : Finset R.EdgeIndex) (e : R.EdgeIndex), e ∉ F →
      genusOneRibbonEulerDefect S C.primalVertexCount
          (fkRectFinsetClusterCount R) F ≤
        genusOneRibbonEulerDefect S C.primalVertexCount
          (fkRectFinsetClusterCount R) (insert e F))
    (F : Finset R.EdgeIndex) :
    fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R F) = 0 ∨
      fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R F) = 2 := by
  have hempty : fkRectFinsetClusterCount R ∅ = C.primalVertexCount := by
    rw [fkRectFinsetClusterCount_empty, hprimal]
  have hfull : fkRectFinsetClusterCount R Finset.univ = 1 :=
    fkRectFinsetClusterCount_univ R
  have hclass := genusOneRibbonEulerDefect_classified S C
    (fkRectFinsetClusterCount R) hgenus hempty hfull hfullBoundary hmono F
  have hid :
      genusOneRibbonEulerDefect S C.primalVertexCount
          (fkRectFinsetClusterCount R) F =
        fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R F) := by
    rw [fkRectEulerHomologyDefect_configurationOfEdges]
    unfold genusOneRibbonEulerDefect
    rw [hprimal, hboundary]
  rwa [hid] at hclass

end

end StatMech.FrontierD
