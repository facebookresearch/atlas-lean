/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectBlackOrbitRibbonSubdivisionIndexGeometry



namespace StatMech.FrontierD

open StatMech.Onsager
open StatMech.Onsager.BaseCase

noncomputable section

set_option maxHeartbeats 1000000 in

theorem fkRectBlackOrbitRibbonSubdivisionWord_get_index
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus)
    (i : Fin (fkRectBlackOrbitMedialRibbonWord R omega d).length)
    (r : Fin (onsAnisotropicStepScale (8 * R.medialTorus.width)
      (8 * R.medialTorus.height)
      (fkRectBlackOrbitMedialRibbonFlatDirection R omega d i))) :
    (fkRectBlackOrbitRibbonSubdivisionWord R omega d).get
        ((fkRectBlackOrbitRibbonSubdivisionIndexEquiv R omega d).symm ⟨i, r⟩) =
      (fkRectBlackOrbitMedialRibbonWord R omega d).get i := by
  have hscale :
      (fun mu => onsAnisotropicStepScale (16 * R.width) (8 * R.height) mu) =
        (fun mu => onsAnisotropicStepScale (8 * R.medialTorus.width)
          (8 * R.medialTorus.height) mu) := by
    funext mu
    fin_cases mu <;> simp [FKRectTorus.medialTorus] <;> ring
  let indexScale := fun j : Fin
      (fkRectBlackOrbitMedialRibbonWord R omega d).length =>
    onsAnisotropicStepScale (16 * R.width) (8 * R.height)
      ((fkRectBlackOrbitMedialRibbonWord R omega d).get j)
  have hIndexScale : indexScale = fun j =>
      onsAnisotropicStepScale (8 * R.medialTorus.width)
        (8 * R.medialTorus.height)
        (fkRectBlackOrbitMedialRibbonFlatDirection R omega d j) := by
    funext j
    rw [fkRectBlackOrbitMedialRibbonFlatDirection_eq_get]
    exact congrFun hscale _
  let r0 : Fin (indexScale i) := Fin.cast (congrFun hIndexScale i).symm r
  unfold fkRectBlackOrbitRibbonSubdivisionWord
  unfold onsAnisotropicDirectionWord
  apply fkRectList_get_flatMap_replicate_finSigma
    (l := fkRectBlackOrbitMedialRibbonWord R omega d)
    (scale := onsAnisotropicStepScale (16 * R.width) (8 * R.height))
    (i := i) (r := r0)
  exact fkRectBlackOrbitRibbonSubdivisionIndexEquiv_symm_val_cast
    R omega d indexScale hIndexScale i r

end

end StatMech.FrontierD
