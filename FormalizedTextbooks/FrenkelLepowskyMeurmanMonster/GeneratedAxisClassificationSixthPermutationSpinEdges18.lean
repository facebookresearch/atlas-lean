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
theorem generatedSixth_permutation_edge_2_26 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![972, 794, 1456, 1465, 1792, 781, 828, 534, 1896, 527, 374, 2078]
      ![1543, 1708, 1092, 256, 832, 480, 640, 512, 256, 512, 0, 0])
      (generatedSixthPermutationSpinLetterModel 3)
      (representativeSpinRowsModel
      ![1383, 1896, 1897, 1888, 882, 1154, 536, 207, 794, 214, 383, 2078]
      ![815, 2, 8, 936, 784, 512, 320, 896, 768, 512, 1024, 0]) := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Check every binary coordinate and all diagonal/polar phase coefficients of this original edge.
/-- The original signed source edge retains its complete coordinate and phase action. -/
theorem generatedSixth_permutation_edge_2_27 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![1383, 1896, 1897, 1888, 882, 1154, 536, 207, 794, 214, 383, 2078]
      ![815, 2, 8, 936, 784, 512, 320, 896, 768, 512, 1024, 0])
      (generatedSixthPermutationSpinLetterModel 0)
      (representativeSpinRowsModel
      ![64, 1152, 1935, 356, 525, 2032, 432, 727, 1699, 9, 319, 2971]
      ![725, 768, 672, 1488, 848, 640, 960, 256, 1792, 1536, 0, 0]) := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Check every binary coordinate and all diagonal/polar phase coefficients of this original edge.
/-- The original signed source edge retains its complete coordinate and phase action. -/
theorem generatedSixth_permutation_edge_2_28 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![64, 1152, 1935, 356, 525, 2032, 432, 727, 1699, 9, 319, 2971]
      ![725, 768, 672, 1488, 848, 640, 960, 256, 1792, 1536, 0, 0])
      (generatedSixthPermutationSpinLetterModel 3)
      (representativeSpinRowsModel
      ![1706, 1699, 838, 1453, 46, 979, 889, 1566, 1152, 1216, 2004, 2971]
      ![1793, 482, 676, 1864, 1936, 608, 1344, 1280, 1536, 512, 1024, 0]) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
