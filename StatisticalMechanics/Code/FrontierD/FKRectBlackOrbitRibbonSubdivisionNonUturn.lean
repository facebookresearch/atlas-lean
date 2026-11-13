/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectBlackOrbitRibbonSubdivisionGeometry



namespace StatMech.FrontierD

open StatMech.Onsager
open StatMech.Onsager.BaseCase

noncomputable section

set_option maxHeartbeats 1000000 in

theorem fkRectBlackOrbitRibbonSubdivisionDirection_nonUturn
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus)
    (k : Fin (fkRectBlackOrbitRibbonSubdivisionWord R omega d).length) :
    fkRectBlackOrbitMedialRibbonFlatDirection R omega d
        (fkRectBlackOrbitRibbonSubdivisionIndexEquiv R omega d (k + 1)).1 ≠
      fkRectBlackOrbitMedialRibbonFlatDirection R omega d
        (fkRectBlackOrbitRibbonSubdivisionIndexEquiv R omega d k).1 + 2 := by
  rw [fkRectBlackOrbitRibbonSubdivisionIndexEquiv_add_one]
  exact fkRectBlackOrbitRibbonSubdivisionDirection_nonUturn_index
    R omega d (fkRectBlackOrbitRibbonSubdivisionIndexEquiv R omega d k)

end

end StatMech.FrontierD
