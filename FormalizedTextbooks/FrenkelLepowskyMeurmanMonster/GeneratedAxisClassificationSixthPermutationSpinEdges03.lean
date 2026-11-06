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
theorem generatedSixth_permutation_edge_0_09 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![2038, 963, 979, 1789, 906, 1885, 209, 691, 1771, 1510, 385, 2919]
      ![30, 1584, 1304, 1032, 544, 1888, 1600, 256, 1792, 1536, 1024, 0])
      (generatedSixthPermutationSpinLetterModel 1)
      (representativeSpinRowsModel
      ![781, 1771, 512, 1838, 1698, 527, 376, 864, 963, 1077, 1199, 2919]
      ![1377, 2008, 1660, 752, 1072, 480, 0, 384, 512, 1024, 0, 0]) := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Check every binary coordinate and all diagonal/polar phase coefficients of this original edge.
/-- The original signed source edge retains its complete coordinate and phase action. -/
theorem generatedSixth_permutation_edge_0_10 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![781, 1771, 512, 1838, 1698, 527, 376, 864, 963, 1077, 1199, 2919]
      ![1377, 2008, 1660, 752, 1072, 480, 0, 384, 512, 1024, 0, 0])
      (generatedSixthPermutationSpinLetterModel 0)
      (representativeSpinRowsModel
      ![1464, 1508, 1362, 1041, 525, 1197, 1999, 536, 1342, 1326, 279, 3079]
      ![62, 1020, 96, 296, 2000, 1664, 1664, 1152, 1792, 1024, 1024, 0]) := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Check every binary coordinate and all diagonal/polar phase coefficients of this original edge.
/-- The original signed source edge retains its complete coordinate and phase action. -/
theorem generatedSixth_permutation_edge_0_11 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![1464, 1508, 1362, 1041, 525, 1197, 1999, 536, 1342, 1326, 279, 3079]
      ![62, 1020, 96, 296, 2000, 1664, 1664, 1152, 1792, 1024, 1024, 0])
      (generatedSixthPermutationSpinLetterModel 0)
      (representativeSpinRowsModel
      ![1743, 2027, 1536, 1383, 794, 1696, 783, 1495, 1117, 323, 2008, 2971]
      ![959, 602, 788, 1152, 1008, 1984, 1856, 1408, 1792, 1536, 0, 0]) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
