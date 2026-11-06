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
theorem generatedSixth_permutation_edge_1_12 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![1065, 979, 161, 1061, 838, 1698, 439, 727, 525, 1885, 846, 2078]
      ![1040, 1520, 608, 1896, 224, 1824, 1280, 0, 1536, 1024, 0, 0])
      (generatedSixthPermutationSpinLetterModel 2)
      (representativeSpinRowsModel
      ![92, 586, 1975, 234, 1057, 643, 1031, 1744, 1075, 1218, 1895, 2971]
      ![2014, 684, 120, 208, 1712, 1536, 1024, 1152, 1280, 1024, 1024, 0]) := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Check every binary coordinate and all diagonal/polar phase coefficients of this original edge.
/-- The original signed source edge retains its complete coordinate and phase action. -/
theorem generatedSixth_permutation_edge_2_00 :
    representativeSpinEdge representativeSpinIdentityModel
      (generatedSixthPermutationSpinLetterModel 1)
      (representativeSpinRowsModel
      ![768, 256, 519, 523, 274, 323, 546, 643, 2, 3, 1036, 2048]
      ![829, 254, 8, 0, 512, 256, 512, 256, 0, 512, 0, 0]) := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Check every binary coordinate and all diagonal/polar phase coefficients of this original edge.
/-- The original signed source edge retains its complete coordinate and phase action. -/
theorem generatedSixth_permutation_edge_2_01 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![768, 256, 519, 523, 274, 323, 546, 643, 2, 3, 1036, 2048]
      ![829, 254, 8, 0, 512, 256, 512, 256, 0, 512, 0, 0])
      (generatedSixthPermutationSpinLetterModel 2)
      (representativeSpinRowsModel
      ![192, 1935, 1154, 1153, 1566, 1885, 1965, 1326, 1464, 1652, 1804, 2255]
      ![1854, 1278, 688, 368, 512, 256, 768, 768, 512, 512, 0, 0]) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
