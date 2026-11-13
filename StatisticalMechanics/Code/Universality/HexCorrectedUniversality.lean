/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.Universality.HexCorrectedConnectiveReduction
import Code.Universality.HexCorrectedHighestCutGeometry
import Code.Universality.HexCorrectedStripExteriorPeriod

namespace StatMech.Universality

open Filter Topology

noncomputable section



theorem hexStandard_connective_constant_of_local_cut_convergence
    (hlocal : ∀ T L (hT : 0 < T), HexCSLocalRelation T L hT)
    (G : ∀ T (hT : 1 ≤ T), HexCSHighestCutGeometry T hT)
    (hconv : ∀ x, 0 < x → x < hexChiE →
      Summable (fun n : ℕ =>
        hlc_sawCountR hexAWStart 1 n * x ^ n)) :
    ∃ kappa : ℝ, 0 < kappa ∧
      Tendsto (fun n => (hexStandardSAWCount n) ^ ((n : ℝ)⁻¹))
        atTop (nhds kappa) ∧
      kappa = Real.sqrt (2 + Real.sqrt 2) := by
  exact hexStandard_connective_constant_of_corrected_data
    hlocal hexCSBoundaryWindowLaw_unconditional
    (hexCS_highestCuts_of_geometry G) hconv

end


end StatMech.Universality
