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
theorem generatedSixth_permutation_edge_2_05 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![3, 1466, 1154, 1090, 1435, 1582, 1259, 1117, 1403, 1652, 443, 2255]
      ![807, 596, 1400, 1984, 336, 640, 1792, 1536, 1280, 1536, 1024, 0])
      (generatedSixthPermutationSpinLetterModel 1)
      (representativeSpinRowsModel
      ![783, 1403, 1871, 1935, 1370, 1065, 1504, 1936, 1466, 1465, 379, 2255]
      ![495, 924, 1036, 1656, 656, 320, 1600, 1024, 1792, 1024, 0, 0]) := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Check every binary coordinate and all diagonal/polar phase coefficients of this original edge.
/-- The original signed source edge retains its complete coordinate and phase action. -/
theorem generatedSixth_permutation_edge_2_06 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![783, 1403, 1871, 1935, 1370, 1065, 1504, 1936, 1466, 1465, 379, 2255]
      ![495, 924, 1036, 1656, 656, 320, 1600, 1024, 1792, 1024, 0, 0])
      (generatedSixthPermutationSpinLetterModel 0)
      (representativeSpinRowsModel
      ![12, 1660, 519, 263, 1057, 371, 1771, 624, 504, 192, 375, 2048]
      ![231, 404, 12, 368, 656, 320, 1472, 1920, 0, 512, 0, 0]) := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Check every binary coordinate and all diagonal/polar phase coefficients of this original edge.
/-- The original signed source edge retains its complete coordinate and phase action. -/
theorem generatedSixth_permutation_edge_2_07 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![12, 1660, 519, 263, 1057, 371, 1771, 624, 504, 192, 375, 2048]
      ![231, 404, 12, 368, 656, 320, 1472, 1920, 0, 512, 0, 0])
      (generatedSixthPermutationSpinLetterModel 1)
      (representativeSpinRowsModel
      ![312, 504, 1207, 1975, 933, 355, 1999, 1216, 1660, 1648, 631, 2048]
      ![1122, 930, 1704, 352, 832, 160, 64, 128, 256, 1536, 1024, 0]) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
