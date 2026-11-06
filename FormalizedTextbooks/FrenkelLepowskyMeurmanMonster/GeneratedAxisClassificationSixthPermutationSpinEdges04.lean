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
theorem generatedSixth_permutation_edge_0_12 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![1743, 2027, 1536, 1383, 794, 1696, 783, 1495, 1117, 323, 2008, 2971]
      ![959, 602, 788, 1152, 1008, 1984, 1856, 1408, 1792, 1536, 0, 0])
      (generatedSixthPermutationSpinLetterModel 0)
      (representativeSpinRowsModel
      ![1453, 838, 214, 1706, 1218, 1466, 527, 1752, 349, 871, 629, 2127]
      ![962, 1900, 1568, 1112, 1696, 320, 1024, 128, 0, 0, 1024, 0]) := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Check every binary coordinate and all diagonal/polar phase coefficients of this original edge.
/-- The original signed source edge retains its complete coordinate and phase action. -/
theorem generatedSixth_permutation_edge_0_13 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![1453, 838, 214, 1706, 1218, 1466, 527, 1752, 349, 871, 629, 2127]
      ![962, 1900, 1568, 1112, 1696, 320, 1024, 128, 0, 0, 1024, 0])
      (generatedSixthPermutationSpinLetterModel 1)
      (representativeSpinRowsModel
      ![570, 349, 1370, 806, 1753, 1465, 1435, 852, 838, 1771, 1033, 2127]
      ![883, 952, 1284, 1048, 1408, 1696, 1472, 896, 1024, 1024, 1024, 0]) := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Check every binary coordinate and all diagonal/polar phase coefficients of this original edge.
/-- The original signed source edge retains its complete coordinate and phase action. -/
theorem generatedSixth_permutation_edge_0_14 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![570, 349, 1370, 806, 1753, 1465, 1435, 852, 838, 1771, 1033, 2127]
      ![883, 952, 1284, 1048, 1408, 1696, 1472, 896, 1024, 1024, 1024, 0])
      (generatedSixthPermutationSpinLetterModel 0)
      (representativeSpinRowsModel
      ![1941, 1038, 3, 1, 720, 864, 1885, 1743, 1516, 1660, 924, 3083]
      ![433, 864, 432, 432, 1696, 1376, 0, 1152, 1280, 512, 1024, 0]) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
