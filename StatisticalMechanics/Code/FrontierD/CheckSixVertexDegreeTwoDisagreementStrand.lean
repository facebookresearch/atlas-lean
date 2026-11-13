/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierD.SixVertexDegreeTwoDisagreementStrand
import Code.FrontierD.SixVertexPairSwitchNoUnitCounterexample

open StatMech.FrontierD

#print axioms existsUnique_mem_ne_of_card_eq_two
#print axioms finsetOther_involutive
#print axioms sixVertexTorusDartBondMate_involutive
#print axioms sixVertexDisagreementBondMate_involutive
#print axioms sixVertexDegreeTwoLocalMate_involutive
#print axioms sixVertexDegreeTwoStrandSuccessor
#print axioms sixVertexDegreeTwoStrandSuccessor_incoming
#print axioms sixVertexOrientedDegreeTwoStrandSuccessor
#print axioms sixVertexOrientedDisagreementDartEquivEdge
#print axioms sum_sixVertexDegreeTwoStrandStepSeamSign_eq_two
#print axioms sum_map_permOrderedAllCycles
#print axioms sixVertexDegreeTwoAllStrandsSeamWord_sum_eq_two
#print axioms sixVertexDegreeTwoStrandSeamWord_unitSteps



example : SixVertexLocallyDegreeTwo
    sixVertexFourByTwoLowArrows sixVertexFourByTwoHighArrows := by
  intro v
  right
  rw [card_sixVertexLocalDisagreementSides]
  exact sixVertexFourByTwo_localDisagreementDegree_two v
