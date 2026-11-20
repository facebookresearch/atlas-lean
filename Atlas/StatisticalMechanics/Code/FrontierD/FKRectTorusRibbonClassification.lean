/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKRectEulerDefectInsertion

open Finset

namespace StatMech.FrontierD

open StatMech.FrontierA

noncomputable section




theorem fkRectEulerHomologyDefect_classified_of_ribbonBoundary
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
    (F : Finset R.EdgeIndex) :
    fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R F) = 0 ∨
      fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R F) = 2 := by
  apply fkRectEulerHomologyDefect_classified_of_ribbon
    R S C hprimal hgenus hboundary hfullBoundary
  intro A e he
  have hA :
      genusOneRibbonEulerDefect S C.primalVertexCount
          (fkRectFinsetClusterCount R) A =
        fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R A) := by
    rw [fkRectEulerHomologyDefect_configurationOfEdges]
    unfold genusOneRibbonEulerDefect
    rw [hprimal, hboundary]
  have hAe :
      genusOneRibbonEulerDefect S C.primalVertexCount
          (fkRectFinsetClusterCount R) (insert e A) =
        fkRectEulerHomologyDefect R
          (fkRectConfigurationOfEdges R (insert e A)) := by
    rw [fkRectEulerHomologyDefect_configurationOfEdges]
    unfold genusOneRibbonEulerDefect
    rw [hprimal, hboundary]
  rw [hA, hAe]
  exact fkRectEulerHomologyDefect_insert_mono R A e he

end

end StatMech.FrontierD
