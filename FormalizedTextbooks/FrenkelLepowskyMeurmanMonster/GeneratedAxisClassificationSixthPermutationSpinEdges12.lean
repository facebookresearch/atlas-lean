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
theorem generatedSixth_permutation_edge_2_08 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![312, 504, 1207, 1975, 933, 355, 1999, 1216, 1660, 1648, 631, 2048]
      ![1122, 930, 1704, 352, 832, 160, 64, 128, 256, 1536, 1024, 0])
      (generatedSixthPermutationSpinLetterModel 2)
      (representativeSpinRowsModel
      ![1179, 1871, 1403, 779, 234, 393, 64, 1152, 1706, 9, 847, 2539]
      ![1102, 142, 12, 200, 688, 672, 192, 1664, 768, 0, 1024, 0]) := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Check every binary coordinate and all diagonal/polar phase coefficients of this original edge.
/-- The original signed source edge retains its complete coordinate and phase action. -/
theorem generatedSixth_permutation_edge_2_09 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![1179, 1871, 1403, 779, 234, 393, 64, 1152, 1706, 9, 847, 2539]
      ![1102, 142, 12, 200, 688, 672, 192, 1664, 768, 0, 1024, 0])
      (generatedSixthPermutationSpinLetterModel 1)
      (representativeSpinRowsModel
      ![1699, 1706, 1702, 214, 271, 1342, 1743, 1885, 1871, 980, 1343, 2539]
      ![275, 1746, 984, 2008, 976, 32, 1856, 384, 512, 1024, 0, 0]) := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Check every binary coordinate and all diagonal/polar phase coefficients of this original edge.
/-- The original signed source edge retains its complete coordinate and phase action. -/
theorem generatedSixth_permutation_edge_2_10 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![1699, 1706, 1702, 214, 271, 1342, 1743, 1885, 1871, 980, 1343, 2539]
      ![275, 1746, 984, 2008, 976, 32, 1856, 384, 512, 1024, 0, 0])
      (generatedSixthPermutationSpinLetterModel 2)
      (representativeSpinRowsModel
      ![1216, 1224, 128, 852, 659, 1965, 526, 1363, 781, 1822, 924, 2191]
      ![1057, 2034, 2012, 2008, 288, 960, 1600, 768, 1024, 0, 1024, 0]) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
