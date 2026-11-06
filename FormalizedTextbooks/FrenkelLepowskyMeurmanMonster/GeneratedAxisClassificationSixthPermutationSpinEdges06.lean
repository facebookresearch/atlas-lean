/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthPermutationSpinPlanData

/-! Three bounded original signed spin edges, with every quadratic sign checked. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private instance (a b c : RepresentativeSpinModel) : Decidable (representativeSpinEdge a b c) :=
  representativeSpinEdgeDecisionFast a b c

set_option maxHeartbeats 2000000 in
-- Check every binary coordinate and all diagonal/polar phase coefficients of this original edge.
/-- The original signed source edge retains its complete coordinate and phase action. -/
theorem generatedSixth_permutation_edge_1_03 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![12, 523, 4, 5, 581, 113, 536, 209, 269, 512, 1549, 2048]
      ![556, 2, 208, 120, 16, 512, 64, 640, 768, 512, 1024, 0])
      (generatedSixthPermutationSpinLetterModel 0)
      (representativeSpinRowsModel
      ![241, 1598, 355, 659, 1096, 564, 1756, 713, 271, 1, 1788, 3069]
      ![71, 12, 576, 536, 352, 928, 384, 768, 1792, 1024, 1024, 0]) := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Check every binary coordinate and all diagonal/polar phase coefficients of this original edge.
/-- The original signed source edge retains its complete coordinate and phase action. -/
theorem generatedSixth_permutation_edge_1_04 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![241, 1598, 355, 659, 1096, 564, 1756, 713, 271, 1, 1788, 3069]
      ![71, 12, 576, 536, 352, 928, 384, 768, 1792, 1024, 1024, 0])
      (generatedSixthPermutationSpinLetterModel 1)
      (representativeSpinRowsModel
      ![270, 271, 1965, 1117, 889, 284, 1035, 1031, 1598, 1743, 1292, 3069]
      ![621, 616, 552, 1088, 560, 1312, 1728, 256, 768, 1536, 0, 0]) := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Check every binary coordinate and all diagonal/polar phase coefficients of this original edge.
/-- The original signed source edge retains its complete coordinate and phase action. -/
theorem generatedSixth_permutation_edge_1_05 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![270, 271, 1965, 1117, 889, 284, 1035, 1031, 1598, 1743, 1292, 3069]
      ![621, 616, 552, 1088, 560, 1312, 1728, 256, 768, 1536, 0, 0])
      (generatedSixthPermutationSpinLetterModel 0)
      (representativeSpinRowsModel
      ![871, 1896, 808, 432, 1653, 613, 267, 12, 1197, 1008, 1643, 2971]
      ![1462, 1532, 1092, 1448, 848, 32, 128, 256, 1536, 512, 0, 0]) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
