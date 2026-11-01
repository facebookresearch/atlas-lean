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
theorem generatedSixth_permutation_edge_2_02 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![192, 1935, 1154, 1153, 1566, 1885, 1965, 1326, 1464, 1652, 1804, 2255]
      ![1854, 1278, 688, 368, 512, 256, 768, 768, 512, 512, 0, 0])
      (generatedSixthPermutationSpinLetterModel 2)
      (representativeSpinRowsModel
      ![691, 1453, 1698, 214, 466, 1679, 1359, 97, 92, 556, 1996, 3083]
      ![1629, 1836, 1220, 368, 1600, 1408, 1984, 256, 512, 1536, 1024, 0]) := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Check every binary coordinate and all diagonal/polar phase coefficients of this original edge.
/-- The original signed source edge retains its complete coordinate and phase action. -/
theorem generatedSixth_permutation_edge_2_03 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![691, 1453, 1698, 214, 466, 1679, 1359, 97, 92, 556, 1996, 3083]
      ![1629, 1836, 1220, 368, 1600, 1408, 1984, 256, 512, 1536, 1024, 0])
      (generatedSixthPermutationSpinLetterModel 1)
      (representativeSpinRowsModel
      ![624, 92, 912, 1508, 1059, 525, 270, 1363, 1453, 1822, 440, 3083]
      ![1073, 2032, 968, 1984, 1472, 1760, 1280, 640, 1280, 0, 1024, 0]) := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Check every binary coordinate and all diagonal/polar phase coefficients of this original edge.
/-- The original signed source edge retains its complete coordinate and phase action. -/
theorem generatedSixth_permutation_edge_2_04 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![624, 92, 912, 1508, 1059, 525, 270, 1363, 1453, 1822, 440, 3083]
      ![1073, 2032, 968, 1984, 1472, 1760, 1280, 640, 1280, 0, 1024, 0])
      (generatedSixthPermutationSpinLetterModel 0)
      (representativeSpinRowsModel
      ![3, 1466, 1154, 1090, 1435, 1582, 1259, 1117, 1403, 1652, 443, 2255]
      ![807, 596, 1400, 1984, 336, 640, 1792, 1536, 1280, 1536, 1024, 0]) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
