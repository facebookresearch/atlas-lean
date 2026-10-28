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
theorem generatedSixth_permutation_edge_2_17 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![145, 1156, 788, 177, 864, 1753, 1698, 1362, 1218, 2032, 1904, 2127]
      ![1262, 1084, 236, 1976, 448, 1408, 1728, 512, 1024, 0, 0, 0])
      (generatedSixthPermutationSpinLetterModel 2)
      (representativeSpinRowsModel
      ![794, 1702, 1696, 336, 1153, 600, 1041, 323, 225, 207, 2017, 3840]
      ![1512, 1164, 136, 104, 896, 512, 1344, 1920, 1280, 512, 0, 0]) := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Check every binary coordinate and all diagonal/polar phase coefficients of this original edge.
/-- The original signed source edge retains its complete coordinate and phase action. -/
theorem generatedSixth_permutation_edge_2_18 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![794, 1702, 1696, 336, 1153, 600, 1041, 323, 225, 207, 2017, 3840]
      ![1512, 1164, 136, 104, 896, 512, 1344, 1920, 1280, 512, 0, 0])
      (generatedSixthPermutationSpinLetterModel 2)
      (representativeSpinRowsModel
      ![1, 4, 1216, 1039, 122, 546, 425, 234, 1326, 453, 1275, 2110]
      ![887, 714, 1168, 1568, 208, 32, 832, 512, 1280, 1024, 1024, 0]) := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Check every binary coordinate and all diagonal/polar phase coefficients of this original edge.
/-- The original signed source edge retains its complete coordinate and phase action. -/
theorem generatedSixth_permutation_edge_2_19 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![1, 4, 1216, 1039, 122, 546, 425, 234, 1326, 453, 1275, 2110]
      ![887, 714, 1168, 1568, 208, 32, 832, 512, 1280, 1024, 1024, 0])
      (generatedSixthPermutationSpinLetterModel 3)
      (representativeSpinRowsModel
      ![1259, 1326, 1280, 1487, 1360, 1154, 995, 298, 4, 5, 1076, 2110]
      ![476, 1286, 156, 1288, 272, 736, 512, 896, 1536, 0, 0, 0]) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
