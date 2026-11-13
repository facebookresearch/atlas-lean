/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectMedialDualShift
import Code.FrontierD.FKRectTorusWindingCountBridge



namespace StatMech.FrontierD

noncomputable section


def fkRectMedialDualShiftColumnEquiv (R : FKRectTorus) :
    Fin R.medialTorus.width ≃ Fin R.medialTorus.width where
  toFun := SixVertexArrows.cyclicPred R.medialTorus.width_pos
  invFun := finitePeriodicSucc R.medialTorus.width_pos
  left_inv := finitePeriodicSucc_cyclicPred R.medialTorus.width_pos
  right_inv := svCyclicPred_finitePeriodicSucc R.medialTorus.width_pos

@[simp] theorem fkRectMedialDualShiftColumnEquiv_apply
    (R : FKRectTorus) (i : Fin R.medialTorus.width) :
    fkRectMedialDualShiftColumnEquiv R i =
      SixVertexArrows.cyclicPred R.medialTorus.width_pos i :=
  rfl

@[simp] theorem fkRectMedialDualShiftDart_verticalSeam
    (R : FKRectTorus) (i : Fin R.medialTorus.width) :
    fkRectMedialDualShiftDart R
        (fkMedialVerticalSeamDart R.medialTorus i) =
      fkMedialVerticalSeamDart R.medialTorus
        (fkRectMedialDualShiftColumnEquiv R i) := by
  rfl


theorem fkMedialCanonicalVerticalSeamSign_dualShift
    (R : FKRectTorus) (i : Fin R.medialTorus.width) :
    fkMedialCanonicalVerticalSeamSign R.medialTorus
        (fkRectMedialDualShiftColumnEquiv R i) =
      -fkMedialCanonicalVerticalSeamSign R.medialTorus i := by
  unfold fkMedialCanonicalVerticalSeamSign fkMedialVerticalSeamDart
    fkMedialCheckerColor fkMedialSideVertical
  simp only [fkRectMedialDualShiftColumnEquiv_apply,
    fkMedialVertexParity_cyclicPred_fst]
  cases fkMedialVertexParity
      (i, svFinLast R.medialTorus.height_pos) <;> rfl



theorem fkMedialLoopCanonicalVerticalFlux_dualShift
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKMedialLoop R.medialTorus
      (fkRectConfigurationToMedialPairing R omega)) :
    fkMedialLoopCanonicalVerticalFlux
        (fkRectConfigurationToMedialPairing R
          (fkRectDualConfigurationEquiv R omega))
        ((fkRectMedialDualShiftGraphIso R omega).connectedComponentEquiv C) =
      -fkMedialLoopCanonicalVerticalFlux
        (fkRectConfigurationToMedialPairing R omega) C := by
  classical
  let pairing := fkRectConfigurationToMedialPairing R omega
  let dualPairing := fkRectConfigurationToMedialPairing R
    (fkRectDualConfigurationEquiv R omega)
  let e := (fkRectMedialDualShiftGraphIso R omega).connectedComponentEquiv
  have hcomponent (i : Fin R.medialTorus.width) :
      (fkMedialLoopGraph R.medialTorus dualPairing).connectedComponentMk
          (fkMedialVerticalSeamDart R.medialTorus
            (fkRectMedialDualShiftColumnEquiv R i)) = e C ↔
        (fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk
          (fkMedialVerticalSeamDart R.medialTorus i) = C := by
    change
      (fkMedialLoopGraph R.medialTorus dualPairing).connectedComponentMk
          ((fkRectMedialDualShiftGraphIso R omega)
            (fkMedialVerticalSeamDart R.medialTorus i)) =
          SimpleGraph.ConnectedComponent.map
            (fkRectMedialDualShiftGraphIso R omega) C ↔ _
    exact SimpleGraph.ConnectedComponent.iso_image_comp_eq_map_iff_eq_comp
  unfold fkMedialLoopCanonicalVerticalFlux
  change (∑ i : Fin R.medialTorus.width,
      if (fkMedialLoopGraph R.medialTorus dualPairing).connectedComponentMk
          (fkMedialVerticalSeamDart R.medialTorus i) = e C then
        fkMedialCanonicalVerticalSeamSign R.medialTorus i else 0) = _
  rw [← (fkRectMedialDualShiftColumnEquiv R).sum_comp]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [if_congr (hcomponent i) rfl rfl,
    fkMedialCanonicalVerticalSeamSign_dualShift]
  split <;> simp_all



theorem fkRectUnorientedVerticalWindingTotal_dual
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectUnorientedVerticalWindingTotal R
        (fkRectDualConfigurationEquiv R omega) =
      fkRectUnorientedVerticalWindingTotal R omega := by
  classical
  unfold fkRectUnorientedVerticalWindingTotal
    fkMedialUnorientedVerticalWindingTotal
  let e := (fkRectMedialDualShiftGraphIso R omega).connectedComponentEquiv
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro C _
  rw [fkMedialLoopCanonicalVerticalFlux_dualShift, Int.natAbs_neg]



theorem fkRectUnorientedVerticalWindingNumber_dual
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectUnorientedVerticalWindingNumber R
        (fkRectDualConfigurationEquiv R omega) =
      fkRectUnorientedVerticalWindingNumber R omega := by
  unfold fkRectUnorientedVerticalWindingNumber
  rw [fkRectUnorientedVerticalWindingTotal_dual]

end

end StatMech.FrontierD
