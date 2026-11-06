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
theorem generatedSixth_permutation_edge_0_03 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![972, 1464, 1465, 1466, 1065, 1370, 1702, 1045, 1935, 1871, 1807, 2255]
      ![1084, 2046, 0, 8, 528, 288, 512, 384, 512, 0, 1024, 0])
      (generatedSixthPermutationSpinLetterModel 0)
      (representativeSpinRowsModel
      ![12, 8, 519, 263, 806, 371, 794, 691, 782, 3, 1795, 2048]
      ![818, 240, 700, 368, 528, 288, 768, 896, 256, 512, 1024, 0]) := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Check every binary coordinate and all diagonal/polar phase coefficients of this original edge.
/-- The original signed source edge retains its complete coordinate and phase action. -/
theorem generatedSixth_permutation_edge_0_04 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![12, 8, 519, 263, 806, 371, 794, 691, 782, 3, 1795, 2048]
      ![818, 240, 700, 368, 528, 288, 768, 896, 256, 512, 1024, 0])
      (generatedSixthPermutationSpinLetterModel 0)
      (representativeSpinRowsModel
      ![1008, 1362, 355, 402, 1061, 597, 1456, 425, 526, 768, 1267, 3069]
      ![1086, 254, 44, 16, 864, 896, 448, 512, 0, 512, 1024, 0]) := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Check every binary coordinate and all diagonal/polar phase coefficients of this original edge.
/-- The original signed source edge retains its complete coordinate and phase action. -/
theorem generatedSixth_permutation_edge_0_05 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![1008, 1362, 355, 402, 1061, 597, 1456, 425, 526, 768, 1267, 3069]
      ![1086, 254, 44, 16, 864, 896, 448, 512, 0, 512, 1024, 0])
      (generatedSixthPermutationSpinLetterModel 0)
      (representativeSpinRowsModel
      ![409, 1057, 841, 46, 214, 1648, 1370, 1049, 1598, 241, 1386, 2971]
      ![368, 1178, 2008, 864, 16, 1920, 1664, 128, 1280, 1536, 1024, 0]) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
