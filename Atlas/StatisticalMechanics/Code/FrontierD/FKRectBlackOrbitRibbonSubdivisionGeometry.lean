/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectBlackOrbitRibbonSubdivisionSiteGeometry
import Code.FrontierD.FKRectBlackOrbitRibbonSubdivisionWordLookup



namespace StatMech.FrontierD

theorem fkRectBlackOrbitRibbonSubdivisionWord_get
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus)
    (k : Fin (fkRectBlackOrbitRibbonSubdivisionWord R omega d).length) :
    (fkRectBlackOrbitRibbonSubdivisionWord R omega d).get k =
      fkRectBlackOrbitMedialRibbonFlatDirection R omega d
        (fkRectBlackOrbitRibbonSubdivisionIndexEquiv R omega d k).1 := by
  let E := fkRectBlackOrbitRibbonSubdivisionIndexEquiv R omega d
  obtain ⟨⟨i, r⟩, rfl⟩ := E.symm.surjective k
  rw [Equiv.apply_symm_apply]
  rw [fkRectBlackOrbitMedialRibbonFlatDirection_eq_get]
  exact fkRectBlackOrbitRibbonSubdivisionWord_get_index R omega d i r

end StatMech.FrontierD
