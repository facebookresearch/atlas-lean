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
theorem generatedSixth_permutation_edge_1_00 :
    representativeSpinEdge representativeSpinIdentityModel
      (generatedSixthPermutationSpinLetterModel 2)
      (representativeSpinRowsModel
      ![161, 1154, 1935, 1423, 1041, 1073, 1217, 1089, 1239, 1147, 1025, 2733]
      ![546, 12, 728, 624, 0, 512, 0, 512, 512, 1024, 0, 0]) := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Check every binary coordinate and all diagonal/polar phase coefficients of this original edge.
/-- The original signed source edge retains its complete coordinate and phase action. -/
theorem generatedSixth_permutation_edge_1_01 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![161, 1154, 1935, 1423, 1041, 1073, 1217, 1089, 1239, 1147, 1025, 2733]
      ![546, 12, 728, 624, 0, 512, 0, 512, 512, 1024, 0, 0])
      (generatedSixthPermutationSpinLetterModel 1)
      (representativeSpinRowsModel
      ![172, 1239, 2007, 1495, 1092, 1077, 1224, 1049, 1154, 1059, 1537, 2733]
      ![527, 14, 12, 0, 16, 0, 64, 128, 256, 1024, 1024, 0]) := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Check every binary coordinate and all diagonal/polar phase coefficients of this original edge.
/-- The original signed source edge retains its complete coordinate and phase action. -/
theorem generatedSixth_permutation_edge_1_02 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![172, 1239, 2007, 1495, 1092, 1077, 1224, 1049, 1154, 1059, 1537, 2733]
      ![527, 14, 12, 0, 16, 0, 64, 128, 256, 1024, 1024, 0])
      (generatedSixthPermutationSpinLetterModel 0)
      (representativeSpinRowsModel
      ![12, 523, 4, 5, 581, 113, 536, 209, 269, 512, 1549, 2048]
      ![556, 2, 208, 120, 16, 512, 64, 640, 768, 512, 1024, 0]) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
