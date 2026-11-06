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
theorem generatedSixth_permutation_edge_0_06 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![409, 1057, 841, 46, 214, 1648, 1370, 1049, 1598, 241, 1386, 2971]
      ![368, 1178, 2008, 864, 16, 1920, 1664, 128, 1280, 1536, 1024, 0])
      (generatedSixthPermutationSpinLetterModel 1)
      (representativeSpinRowsModel
      ![1743, 1598, 1536, 1383, 713, 1756, 672, 336, 1057, 1464, 1549, 2971]
      ![1377, 2, 1936, 1584, 1264, 416, 1344, 512, 1792, 0, 1024, 0]) := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Check every binary coordinate and all diagonal/polar phase coefficients of this original edge.
/-- The original signed source edge retains its complete coordinate and phase action. -/
theorem generatedSixth_permutation_edge_0_07 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![1743, 1598, 1536, 1383, 713, 1756, 672, 336, 1057, 1464, 1549, 2971]
      ![1377, 2, 1936, 1584, 1264, 416, 1344, 512, 1792, 0, 1024, 0])
      (generatedSixthPermutationSpinLetterModel 2)
      (representativeSpinRowsModel
      ![323, 355, 1362, 234, 523, 1239, 818, 610, 453, 1326, 194, 3079]
      ![110, 962, 2040, 1544, 1264, 480, 1408, 384, 1792, 1536, 1024, 0]) := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Check every binary coordinate and all diagonal/polar phase coefficients of this original edge.
/-- The original signed source edge retains its complete coordinate and phase action. -/
theorem generatedSixth_permutation_edge_0_08 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![323, 355, 1362, 234, 523, 1239, 818, 610, 453, 1326, 194, 3079]
      ![110, 962, 2040, 1544, 1264, 480, 1408, 384, 1792, 1536, 1024, 0])
      (generatedSixthPermutationSpinLetterModel 2)
      (representativeSpinRowsModel
      ![2038, 963, 979, 1789, 906, 1885, 209, 691, 1771, 1510, 385, 2919]
      ![30, 1584, 1304, 1032, 544, 1888, 1600, 256, 1792, 1536, 1024, 0]) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
