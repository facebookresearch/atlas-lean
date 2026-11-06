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
theorem generatedSixth_permutation_edge_2_14 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![1096, 1948, 9, 1706, 393, 234, 1154, 145, 779, 1403, 155, 2539]
      ![1304, 1738, 736, 784, 720, 352, 64, 1664, 1024, 1024, 0, 0])
      (generatedSixthPermutationSpinLetterModel 2)
      (representativeSpinRowsModel
      ![1075, 1942, 781, 1654, 1370, 1456, 192, 81, 1756, 4, 1235, 3584]
      ![1566, 510, 8, 1296, 304, 192, 1152, 1152, 1280, 1536, 1024, 0]) := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Check every binary coordinate and all diagonal/polar phase coefficients of this original edge.
/-- The original signed source edge retains its complete coordinate and phase action. -/
theorem generatedSixth_permutation_edge_2_15 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![1075, 1942, 781, 1654, 1370, 1456, 192, 81, 1756, 4, 1235, 3584]
      ![1566, 510, 8, 1296, 304, 192, 1152, 1152, 1280, 1536, 1024, 0])
      (generatedSixthPermutationSpinLetterModel 3)
      (representativeSpinRowsModel
      ![1752, 1756, 172, 1495, 1040, 1465, 546, 1008, 1942, 933, 424, 3584]
      ![463, 1214, 12, 688, 400, 1600, 192, 512, 512, 1024, 1024, 0]) := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Check every binary coordinate and all diagonal/polar phase coefficients of this original edge.
/-- The original signed source edge retains its complete coordinate and phase action. -/
theorem generatedSixth_permutation_edge_2_16 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![1752, 1756, 172, 1495, 1040, 1465, 546, 1008, 1942, 933, 424, 3584]
      ![463, 1214, 12, 688, 400, 1600, 192, 512, 512, 1024, 1024, 0])
      (generatedSixthPermutationSpinLetterModel 2)
      (representativeSpinRowsModel
      ![145, 1156, 788, 177, 864, 1753, 1698, 1362, 1218, 2032, 1904, 2127]
      ![1262, 1084, 236, 1976, 448, 1408, 1728, 512, 1024, 0, 0, 0]) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
