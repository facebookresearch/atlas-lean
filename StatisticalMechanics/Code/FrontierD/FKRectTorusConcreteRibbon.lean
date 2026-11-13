/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectTorusRibbonClassification
import Code.FrontierD.FKRectMedialClosedCycles










open Equiv Finset

namespace StatMech.FrontierD

open StatMech.FrontierA

noncomputable section

variable {T : EvenTorus}


theorem fkMedialBlackDartSwap_vertex
    (v : T.Vertex) (d : FKMedialBlackDart T) :
    ((fkMedialBlackDartSwap v d).1).1 = d.1.1 := by
  by_cases h0 : d = fkMedialBlackDart0 v
  · subst d
    simp [fkMedialBlackDartSwap, fkMedialBlackDart0,
      fkMedialBlackDart1]
  by_cases h1 : d = fkMedialBlackDart1 v
  · subst d
    simp [fkMedialBlackDartSwap, fkMedialBlackDart0,
      fkMedialBlackDart1]
  rw [fkMedialBlackDartSwap,
    Equiv.swap_apply_of_ne_of_ne h0 h1]


theorem fkMedialBlackDartSwap_apply_of_vertex_ne
    (v : T.Vertex) (d : FKMedialBlackDart T) (hd : d.1.1 ≠ v) :
    fkMedialBlackDartSwap v d = d := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h
    exact hd (congrArg (fun x : FKMedialBlackDart T => x.1.1) h)
  · intro h
    exact hd (congrArg (fun x : FKMedialBlackDart T => x.1.1) h)


theorem fkMedialBlackDartSwap_commute
    {v w : T.Vertex} (hvw : v ≠ w) :
    Commute (fkMedialBlackDartSwap v) (fkMedialBlackDartSwap w) := by
  show fkMedialBlackDartSwap v * fkMedialBlackDartSwap w =
    fkMedialBlackDartSwap w * fkMedialBlackDartSwap v
  apply Equiv.ext
  intro d
  simp only [Equiv.Perm.mul_apply]
  by_cases hdv : d.1.1 = v
  · have hdw : d.1.1 ≠ w := fun h => hvw (hdv.symm.trans h)
    rw [fkMedialBlackDartSwap_apply_of_vertex_ne w d hdw]
    have hsw : ((fkMedialBlackDartSwap v d).1).1 ≠ w := by
      rw [fkMedialBlackDartSwap_vertex v d]
      exact hdw
    rw [fkMedialBlackDartSwap_apply_of_vertex_ne w _ hsw]
  · by_cases hdw : d.1.1 = w
    · rw [fkMedialBlackDartSwap_apply_of_vertex_ne v d hdv]
      have hsv : ((fkMedialBlackDartSwap w d).1).1 ≠ v := by
        rw [fkMedialBlackDartSwap_vertex w d]
        exact hdv
      rw [fkMedialBlackDartSwap_apply_of_vertex_ne v _ hsv]
    · simp only [fkMedialBlackDartSwap_apply_of_vertex_ne v d hdv,
        fkMedialBlackDartSwap_apply_of_vertex_ne w d hdw]


noncomputable def fkRectRibbonSystem (R : FKRectTorus) :
    RibbonPermutationSystem R.EdgeIndex
      (FKMedialBlackDart R.medialTorus) where
  rotation := fkMedialBlackBoundaryPerm (fkRectClosedMedialPairing R)
  edgeFlip := fun e =>
    fkMedialBlackDartSwap (fkRectMedialVertexOfEdge R e)
  edgeFlip_isSwap := fun e => fkMedialBlackDartSwap_isSwap _
  edgeFlip_commute := by
    intro e f hef
    apply fkMedialBlackDartSwap_commute
    intro hv
    apply hef
    exact (fkRectTorusMedialEdgeEquiv R).symm.injective hv



theorem ribbonBoundaryPerm_insert_right
    {E D : Type*} [DecidableEq E] [Fintype D] [DecidableEq D]
    (S : RibbonPermutationSystem E D) (F : Finset E) (e : E)
    (he : e ∉ F) :
    S.boundaryPerm (insert e F) = S.boundaryPerm F * S.edgeFlip e := by
  have hcomm : Commute (S.edgeFlip e) (S.partialEdgeFlip F) := by
    unfold RibbonPermutationSystem.partialEdgeFlip
    apply Finset.noncommProd_commute
    intro f hf
    exact S.edgeFlip_commute e f fun h => he (h ▸ hf)
  rw [RibbonPermutationSystem.boundaryPerm,
    S.partialEdgeFlip_insert F e (by simpa using he),
    RibbonPermutationSystem.boundaryPerm]
  rw [hcomm.eq]
  simp only [mul_assoc]



theorem fkRectRibbonSystem_boundaryPerm
    (R : FKRectTorus) (F : Finset R.EdgeIndex) :
    (fkRectRibbonSystem R).boundaryPerm F =
      fkMedialBlackBoundaryPerm
        (fkRectConfigurationToMedialPairing R
          (fkRectConfigurationOfEdges R F)) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      rw [RibbonPermutationSystem.boundaryPerm_empty,
        fkRectConfigurationToMedialPairing_empty]
      rfl
  | @insert e F he ih =>
      rw [ribbonBoundaryPerm_insert_right (fkRectRibbonSystem R) F e he,
        fkRectConfigurationToMedialPairing_insert R F e he,
        fkMedialBlackBoundaryPerm_toggle, ih]
      rfl


theorem fkRectRibbonSystem_boundaryComponents
    (R : FKRectTorus) (F : Finset R.EdgeIndex) :
    (fkRectRibbonSystem R).boundaryComponents F =
      fkRectMedialLoopCount R (fkRectConfigurationOfEdges R F) := by
  unfold RibbonPermutationSystem.boundaryComponents fkRectMedialLoopCount
  rw [fkRectRibbonSystem_boundaryPerm,
    permCycleCount_fkMedialBlackBoundaryPerm]


noncomputable def fkRectCellularRibbonDualData (R : FKRectTorus) :
    CellularRibbonDualData (fkRectRibbonSystem R) where
  primalVertexCount := Fintype.card R.Vertex
  dualVertexCount := fkRectTorusCellularFaceCount R
  genus := 1
  rotationCycles_eq_primalVertexCount := by
    change StatMech.FrontierA.permCycleCount
        (fkMedialBlackBoundaryPerm (fkRectClosedMedialPairing R)) = _
    rw [permCycleCount_fkMedialBlackBoundaryPerm]
    simpa [fkRectMedialLoopCount,
      fkRectConfigurationToMedialPairing_empty] using
      fkRectMedialLoopCount_empty R
  cellularEuler := fkRectTorus_cellularEuler_genus_one R


theorem fkRectEulerHomologyDefect_classified_of_concreteRibbon
    (R : FKRectTorus) (F : Finset R.EdgeIndex) :
    fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R F) = 0 ∨
      fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R F) = 2 := by
  apply fkRectEulerHomologyDefect_classified_of_ribbonBoundary
    R (fkRectRibbonSystem R) (fkRectCellularRibbonDualData R)
  · rfl
  · rfl
  · exact fkRectRibbonSystem_boundaryComponents R
  · rw [fkRectRibbonSystem_boundaryComponents,
      fkRectMedialLoopCount_univ]
    rfl

end

end StatMech.FrontierD
