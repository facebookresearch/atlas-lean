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
theorem generatedSixth_permutation_edge_0_00 :
    representativeSpinEdge representativeSpinIdentityModel
      (generatedSixthPermutationSpinLetterModel 1)
      (representativeSpinRowsModel
      ![768, 256, 519, 523, 274, 323, 546, 643, 2, 3, 1036, 2048]
      ![829, 254, 8, 0, 512, 256, 512, 256, 0, 512, 0, 0]) := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Check every binary coordinate and all diagonal/polar phase coefficients of this original edge.
/-- The original signed source edge retains its complete coordinate and phase action. -/
theorem generatedSixth_permutation_edge_0_01 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![768, 256, 519, 523, 274, 323, 546, 643, 2, 3, 1036, 2048]
      ![829, 254, 8, 0, 512, 256, 512, 256, 0, 512, 0, 0])
      (generatedSixthPermutationSpinLetterModel 2)
      (representativeSpinRowsModel
      ![192, 1935, 1154, 1153, 1566, 1885, 1965, 1326, 1464, 1652, 1804, 2255]
      ![1854, 1278, 688, 368, 512, 256, 768, 768, 512, 512, 0, 0]) := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Check every binary coordinate and all diagonal/polar phase coefficients of this original edge.
/-- The original signed source edge retains its complete coordinate and phase action. -/
theorem generatedSixth_permutation_edge_0_02 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![192, 1935, 1154, 1153, 1566, 1885, 1965, 1326, 1464, 1652, 1804, 2255]
      ![1854, 1278, 688, 368, 512, 256, 768, 768, 512, 512, 0, 0])
      (generatedSixthPermutationSpinLetterModel 1)
      (representativeSpinRowsModel
      ![972, 1464, 1465, 1466, 1065, 1370, 1702, 1045, 1935, 1871, 1807, 2255]
      ![1084, 2046, 0, 8, 528, 288, 512, 384, 512, 0, 1024, 0]) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
