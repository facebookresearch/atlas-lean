/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectBlackOrbitRibbonSubdivisionCodeDirectionZero
import Code.FrontierD.FKRectBlackOrbitRibbonSubdivisionCodeDirectionOne
import Code.FrontierD.FKRectBlackOrbitRibbonSubdivisionCodeDirectionTwo
import Code.FrontierD.FKRectBlackOrbitRibbonSubdivisionCodeDirectionThree



namespace StatMech.FrontierD

open StatMech.Onsager
open StatMech.Onsager.BaseCase

noncomputable section

set_option maxHeartbeats 500000 in
theorem fkRectBlackOrbitRibbonSubdivisionCode_injective
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    Function.Injective
      (fkRectBlackOrbitRibbonSubdivisionCode R omega d) := by
  intro z w h
  rcases fkRectFinFour_cases
      (fkRectBlackOrbitMedialRibbonFlatDirection R omega d z.1) with
    hz | hz | hz | hz
  · exact fkRectBlackOrbitRibbonSubdivisionCode_eq_of_direction_zero
      R omega d z w hz h
  · exact fkRectBlackOrbitRibbonSubdivisionCode_eq_of_direction_one
      R omega d z w hz h
  · exact fkRectBlackOrbitRibbonSubdivisionCode_eq_of_direction_two
      R omega d z w hz h
  · exact fkRectBlackOrbitRibbonSubdivisionCode_eq_of_direction_three
      R omega d z w hz h

end

end StatMech.FrontierD
