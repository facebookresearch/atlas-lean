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
theorem generatedSixth_permutation_edge_1_06 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![871, 1896, 808, 432, 1653, 613, 267, 12, 1197, 1008, 1643, 2971]
      ![1462, 1532, 1092, 1448, 848, 32, 128, 256, 1536, 512, 0, 0])
      (generatedSixthPermutationSpinLetterModel 0)
      (representativeSpinRowsModel
      ![1648, 1652, 972, 390, 30, 1040, 1639, 263, 738, 664, 27, 2094]
      ![1072, 480, 1652, 1200, 480, 1024, 1728, 1792, 0, 1536, 0, 0]) := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Check every binary coordinate and all diagonal/polar phase coefficients of this original edge.
/-- The original signed source edge retains its complete coordinate and phase action. -/
theorem generatedSixth_permutation_edge_1_07 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![1648, 1652, 972, 390, 30, 1040, 1639, 263, 738, 664, 27, 2094]
      ![1072, 480, 1652, 1200, 480, 1024, 1728, 1792, 0, 1536, 0, 0])
      (generatedSixthPermutationSpinLetterModel 1)
      (representativeSpinRowsModel
      ![122, 738, 336, 794, 1160, 1153, 252, 923, 1652, 4, 593, 2094]
      ![1098, 938, 2040, 1952, 1680, 1152, 1984, 1536, 1792, 1024, 1024, 0]) := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Check every binary coordinate and all diagonal/polar phase coefficients of this original edge.
/-- The original signed source edge retains its complete coordinate and phase action. -/
theorem generatedSixth_permutation_edge_1_08 :
    representativeSpinEdge
      (representativeSpinRowsModel
      ![122, 738, 336, 794, 1160, 1153, 252, 923, 1652, 4, 593, 2094]
      ![1098, 938, 2040, 1952, 1680, 1152, 1984, 1536, 1792, 1024, 1024, 0])
      (generatedSixthPermutationSpinLetterModel 0)
      (representativeSpinRowsModel
      ![788, 192, 145, 1423, 1753, 9, 458, 871, 2034, 586, 325, 3840]
      ![869, 246, 232, 1448, 32, 1024, 128, 1152, 1536, 512, 0, 0]) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
