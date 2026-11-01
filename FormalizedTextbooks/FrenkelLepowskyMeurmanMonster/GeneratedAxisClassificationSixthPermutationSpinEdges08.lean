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
theorem generatedSixth_permutation_edge_1_09 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![788, 192, 145, 1423, 1753, 9, 458, 871, 2034, 586, 325, 3840]
      ![869, 246, 232, 1448, 32, 1024, 128, 1152, 1536, 512, 0, 0])
      (generatedSixthPermutationSpinLetterModel 1)
      (representativeSpinRowsModel
      ![1464, 2034, 271, 1041, 491, 1516, 643, 761, 192, 980, 1115, 3840]
      ![1264, 628, 744, 1488, 480, 864, 384, 896, 1536, 1024, 0, 0]) := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Check every binary coordinate and all diagonal/polar phase coefficients of this original edge.
/-- The original signed source edge retains its complete coordinate and phase action. -/
theorem generatedSixth_permutation_edge_1_10 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![1464, 2034, 271, 1041, 491, 1516, 643, 761, 192, 980, 1115, 3840]
      ![1264, 628, 744, 1488, 480, 864, 384, 896, 1536, 1024, 0, 0])
      (generatedSixthPermutationSpinLetterModel 2)
      (representativeSpinRowsModel
      ![685, 336, 738, 310, 8, 1508, 409, 864, 1679, 1156, 483, 2919]
      ![2036, 162, 536, 984, 256, 1952, 1920, 640, 768, 512, 0, 0]) := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Check every binary coordinate and all diagonal/polar phase coefficients of this original edge.
/-- The original signed source edge retains its complete coordinate and phase action. -/
theorem generatedSixth_permutation_edge_1_11 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![685, 336, 738, 310, 8, 1508, 409, 864, 1679, 1156, 483, 2919]
      ![2036, 162, 536, 984, 256, 1952, 1920, 640, 768, 512, 0, 0])
      (generatedSixthPermutationSpinLetterModel 2)
      (representativeSpinRowsModel
      ![1065, 979, 161, 1061, 838, 1698, 439, 727, 525, 1885, 846, 2078]
      ![1040, 1520, 608, 1896, 224, 1824, 1280, 0, 1536, 1024, 0, 0]) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
