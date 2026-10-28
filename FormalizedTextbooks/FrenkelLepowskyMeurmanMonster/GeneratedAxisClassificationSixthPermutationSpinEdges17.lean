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
theorem generatedSixth_permutation_edge_2_23 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![439, 685, 62, 923, 172, 912, 781, 1277, 161, 48, 240, 2127]
      ![385, 594, 976, 1288, 16, 256, 320, 512, 1536, 512, 0, 0])
      (generatedSixthPermutationSpinLetterModel 2)
      (representativeSpinRowsModel
      ![1754, 1696, 1059, 1043, 491, 635, 1719, 586, 1160, 64, 327, 3328]
      ![918, 1940, 1692, 984, 720, 736, 320, 640, 1280, 0, 0, 0]) := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Check every binary coordinate and all diagonal/polar phase coefficients of this original edge.
/-- The original signed source edge retains its complete coordinate and phase action. -/
theorem generatedSixth_permutation_edge_2_24 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![1754, 1696, 1059, 1043, 491, 635, 1719, 586, 1160, 64, 327, 3328]
      ![918, 1940, 1692, 984, 720, 736, 320, 640, 1280, 0, 0, 0])
      (generatedSixthPermutationSpinLetterModel 2)
      (representativeSpinRowsModel
      ![1771, 1453, 1935, 1999, 1654, 1037, 864, 298, 8, 9, 1949, 2971]
      ![350, 1444, 1772, 464, 768, 320, 0, 0, 1280, 1024, 0, 0]) := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Check every binary coordinate and all diagonal/polar phase coefficients of this original edge.
/-- The original signed source edge retains its complete coordinate and phase action. -/
theorem generatedSixth_permutation_edge_2_25 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![1771, 1453, 1935, 1999, 1654, 1037, 864, 298, 8, 9, 1949, 2971]
      ![350, 1444, 1772, 464, 768, 320, 0, 0, 1280, 1024, 0, 0])
      (generatedSixthPermutationSpinLetterModel 2)
      (representativeSpinRowsModel
      ![972, 794, 1456, 1465, 1792, 781, 828, 534, 1896, 527, 374, 2078]
      ![1543, 1708, 1092, 256, 832, 480, 640, 512, 256, 512, 0, 0]) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
