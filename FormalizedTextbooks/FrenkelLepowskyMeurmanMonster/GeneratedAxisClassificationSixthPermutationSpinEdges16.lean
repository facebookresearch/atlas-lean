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
theorem generatedSixth_permutation_edge_2_20 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![1259, 1326, 1280, 1487, 1360, 1154, 995, 298, 4, 5, 1076, 2110]
      ![476, 1286, 156, 1288, 272, 736, 512, 896, 1536, 0, 0, 0])
      (generatedSixthPermutationSpinLetterModel 0)
      (representativeSpinRowsModel
      ![2032, 1059, 1696, 1466, 356, 466, 1310, 713, 1035, 207, 964, 3840]
      ![936, 1894, 104, 1896, 576, 32, 64, 640, 1536, 1536, 0, 0]) := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Check every binary coordinate and all diagonal/polar phase coefficients of this original edge.
/-- The original signed source edge retains its complete coordinate and phase action. -/
theorem generatedSixth_permutation_edge_2_21 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![2032, 1059, 1696, 1466, 356, 466, 1310, 713, 1035, 207, 964, 3840]
      ![936, 1894, 104, 1896, 576, 32, 64, 640, 1536, 1536, 0, 0])
      (generatedSixthPermutationSpinLetterModel 0)
      (representativeSpinRowsModel
      ![145, 161, 788, 177, 672, 182, 269, 2007, 685, 794, 853, 2127]
      ![911, 510, 1928, 624, 0, 768, 832, 512, 1280, 1536, 0, 0]) := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Check every binary coordinate and all diagonal/polar phase coefficients of this original edge.
/-- The original signed source edge retains its complete coordinate and phase action. -/
theorem generatedSixth_permutation_edge_2_22 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![145, 161, 788, 177, 672, 182, 269, 2007, 685, 794, 853, 2127]
      ![911, 510, 1928, 624, 0, 768, 832, 512, 1280, 1536, 0, 0])
      (generatedSixthPermutationSpinLetterModel 3)
      (representativeSpinRowsModel
      ![439, 685, 62, 923, 172, 912, 781, 1277, 161, 48, 240, 2127]
      ![385, 594, 976, 1288, 16, 256, 320, 512, 1536, 512, 0, 0]) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
