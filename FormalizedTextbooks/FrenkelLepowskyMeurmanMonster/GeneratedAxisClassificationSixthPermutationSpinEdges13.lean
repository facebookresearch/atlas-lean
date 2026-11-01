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
theorem generatedSixth_permutation_edge_2_11 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![1216, 1224, 128, 852, 659, 1965, 526, 1363, 781, 1822, 924, 2191]
      ![1057, 2034, 2012, 2008, 288, 960, 1600, 768, 1024, 0, 1024, 0])
      (generatedSixthPermutationSpinLetterModel 1)
      (representativeSpinRowsModel
      ![1043, 781, 1942, 1090, 1366, 267, 1147, 581, 1224, 8, 72, 2191]
      ![457, 168, 1504, 1240, 1312, 192, 512, 1792, 768, 1024, 0, 0]) := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Check every binary coordinate and all diagonal/polar phase coefficients of this original edge.
/-- The original signed source edge retains its complete coordinate and phase action. -/
theorem generatedSixth_permutation_edge_2_12 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![1043, 781, 1942, 1090, 1366, 267, 1147, 581, 1224, 8, 72, 2191]
      ![457, 168, 1504, 1240, 1312, 192, 512, 1792, 768, 1024, 0, 0])
      (generatedSixthPermutationSpinLetterModel 0)
      (representativeSpinRowsModel
      ![1648, 779, 1702, 5, 1310, 1117, 525, 1598, 1948, 980, 1592, 2539]
      ![1838, 606, 304, 1240, 1216, 800, 64, 1536, 1024, 512, 1024, 0]) := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Check every binary coordinate and all diagonal/polar phase coefficients of this original edge.
/-- The original signed source edge retains its complete coordinate and phase action. -/
theorem generatedSixth_permutation_edge_2_13 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![1648, 779, 1702, 5, 1310, 1117, 525, 1598, 1948, 980, 1592, 2539]
      ![1838, 606, 304, 1240, 1216, 800, 64, 1536, 1024, 512, 1024, 0])
      (generatedSixthPermutationSpinLetterModel 1)
      (representativeSpinRowsModel
      ![1096, 1948, 9, 1706, 393, 234, 1154, 145, 779, 1403, 155, 2539]
      ![1304, 1738, 736, 784, 720, 352, 64, 1664, 1024, 1024, 0, 0]) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
