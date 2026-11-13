/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheAnalyticCandidateSheet









open Filter Topology

namespace StatMech.FrontierD

noncomputable section

theorem tendsto_sixVertexFiniteDensityContinuumErrorOfLower
    (c : Real) {lower : Real} (hlower : 0 < lower) :
    Tendsto (fun N : Nat =>
      sixVertexFiniteDensityContinuumErrorOfLower c N lower)
      atTop (nhds 0) := by
  let A := sixVertexRootDensityKernelLipschitzBound c *
    sixVertexFiniteRootDensityUniformBound c / lower
  have h := tendsto_const_div_atTop_nhds_zero_nat A
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hN0 : (N : Real) ≠ 0 := by exact_mod_cast hN.ne'
  dsimp [A, sixVertexFiniteDensityContinuumErrorOfLower]
  field_simp [hN0, hlower.ne', Real.pi_ne_zero]

theorem tendsto_sixVertexSymmetricJacobianDiagonalErrorOfLower
    (c : Real) {lower : Real} (hlower : 0 < lower) :
    Tendsto (fun N : Nat =>
      sixVertexSymmetricJacobianDiagonalErrorOfLower c N lower)
      atTop (nhds 0) := by
  let A := 4 * Real.pi *
      (sixVertexFiniteRootDensityLipschitzConstant c : Real) / lower ^ 2 +
    2 * (sixVertexAnisotropyMagnitude c /
      (sixVertexAnisotropyMagnitude c - 1)) / lower
  have h := tendsto_const_div_atTop_nhds_zero_nat A
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hN0 : (N : Real) ≠ 0 := by exact_mod_cast hN.ne'
  dsimp [A, sixVertexSymmetricJacobianDiagonalErrorOfLower]
  field_simp [hN0, hlower.ne']

theorem tendsto_sixVertexSymmetricJacobianOffDiagonalErrorOfLower
    (c : Real) {lower : Real} (hlower : 0 < lower) :
    Tendsto (fun N : Nat =>
      sixVertexSymmetricJacobianOffDiagonalErrorOfLower c N lower)
      atTop (nhds 0) := by
  let A := ((2 * Real.pi) *
      (sixVertexSymmetricScatteringLipschitzConstant c : Real) +
    2 * (sixVertexAnisotropyMagnitude c /
      (sixVertexAnisotropyMagnitude c - 1))) / lower
  have h := tendsto_const_div_atTop_nhds_zero_nat A
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hN0 : (N : Real) ≠ 0 := by exact_mod_cast hN.ne'
  dsimp [A, sixVertexSymmetricJacobianOffDiagonalErrorOfLower]
  field_simp [hN0, hlower.ne']

theorem tendsto_sixVertexSymmetricJacobianTotalErrorOfLower
    (c : Real) {lower : Real} (hlower : 0 < lower) :
    Tendsto (fun N : Nat =>
      sixVertexSymmetricJacobianTotalErrorOfLower c N lower)
      atTop (nhds 0) := by
  simpa only [sixVertexSymmetricJacobianTotalErrorOfLower, zero_add] using
    (tendsto_sixVertexSymmetricJacobianDiagonalErrorOfLower c hlower).add
      (tendsto_sixVertexSymmetricJacobianOffDiagonalErrorOfLower c hlower)


def sixVertexDensityGaugeOuterRadius (c rhoLower : Real) : Real :=
  rhoLower * ((sixVertexAnisotropyMagnitude c - 1) /
    sixVertexRootDensityScale c) / 4



def sixVertexDensityGaugeInnerRadius (c rhoLower : Real) : Real :=
  ((sixVertexRootDensityContractionRate c + 1) / 2) *
    sixVertexDensityGaugeOuterRadius c rhoLower

theorem sixVertexDensityGaugeOuterRadius_pos
    {c rhoLower : Real} (hc : 2 < c) (hrho : 0 < rhoLower) :
    0 < sixVertexDensityGaugeOuterRadius c rhoLower := by
  unfold sixVertexDensityGaugeOuterRadius
  exact div_pos
    (mul_pos hrho (div_pos
      (sub_pos.mpr (one_lt_sixVertexAnisotropyMagnitude hc))
      (sixVertexRootDensityScale_pos hc))) (by norm_num)

theorem sixVertexDensityGaugeInner_lt_outer
    {c rhoLower : Real} (hc : 2 < c) (hrho : 0 < rhoLower) :
    sixVertexDensityGaugeInnerRadius c rhoLower <
      sixVertexDensityGaugeOuterRadius c rhoLower := by
  have hrate := sixVertexRootDensityContractionRate_mem_Ico hc
  have houter := sixVertexDensityGaugeOuterRadius_pos hc hrho
  unfold sixVertexDensityGaugeInnerRadius
  nlinarith [hrate.2]

theorem sixVertexDensityGaugeOuterRadius_le_half
    {c rhoLower : Real} (hc : 2 < c) (hrho : 0 ≤ rhoLower) :
    sixVertexDensityGaugeOuterRadius c rhoLower ≤
      rhoLower * ((sixVertexAnisotropyMagnitude c - 1) /
        sixVertexRootDensityScale c) / 2 := by
  let w := (sixVertexAnisotropyMagnitude c - 1) /
    sixVertexRootDensityScale c
  have hw : 0 < w := div_pos
    (sub_pos.mpr (one_lt_sixVertexAnisotropyMagnitude hc))
    (sixVertexRootDensityScale_pos hc)
  unfold sixVertexDensityGaugeOuterRadius
  dsimp [w] at hw
  nlinarith



theorem eventually_sixVertexDensityGaugeNumericalMargins
    {c rhoLower : Real} (hc : 2 < c) (hrho : 0 < rhoLower) :
    ∀ᶠ N : Nat in atTop,
      sixVertexRootDensityContractionRate c *
          sixVertexDensityGaugeOuterRadius c rhoLower +
            sixVertexFiniteDensityContinuumErrorOfLower c N (rhoLower / 2) ≤
        sixVertexDensityGaugeInnerRadius c rhoLower ∧
      sixVertexSymmetricScatteringBoundaryBound c +
          2 * sixVertexSymmetricJacobianTotalErrorOfLower c N (rhoLower / 2) <
        2 * Real.pi := by
  have hlower : 0 < rhoLower / 2 := by positivity
  have herr := tendsto_sixVertexFiniteDensityContinuumErrorOfLower c hlower
  have hjac := tendsto_sixVertexSymmetricJacobianTotalErrorOfLower c hlower
  have hrate := sixVertexRootDensityContractionRate_mem_Ico hc
  have houter := sixVertexDensityGaugeOuterRadius_pos hc hrho
  have hgap : sixVertexRootDensityContractionRate c *
      sixVertexDensityGaugeOuterRadius c rhoLower <
        sixVertexDensityGaugeInnerRadius c rhoLower := by
    unfold sixVertexDensityGaugeInnerRadius
    nlinarith [hrate.2]
  have hboundary := sixVertexSymmetricScatteringBoundaryBound_lt_two_pi
    (c := c)
  have herrEventually : ∀ᶠ N : Nat in atTop,
      sixVertexRootDensityContractionRate c *
          sixVertexDensityGaugeOuterRadius c rhoLower +
            sixVertexFiniteDensityContinuumErrorOfLower c N (rhoLower / 2) <
        sixVertexDensityGaugeInnerRadius c rhoLower := by
    have hopen : Set.Iio
        (sixVertexDensityGaugeInnerRadius c rhoLower -
          sixVertexRootDensityContractionRate c *
            sixVertexDensityGaugeOuterRadius c rhoLower) ∈ nhds 0 :=
      Iio_mem_nhds (by linarith)
    filter_upwards [herr.eventually hopen] with N hN
    change sixVertexFiniteDensityContinuumErrorOfLower c N (rhoLower / 2) < _ at hN
    linarith
  have hjacEventually : ∀ᶠ N : Nat in atTop,
      sixVertexSymmetricScatteringBoundaryBound c +
          2 * sixVertexSymmetricJacobianTotalErrorOfLower c N (rhoLower / 2) <
        2 * Real.pi := by
    have hopen : Set.Iio
        ((2 * Real.pi - sixVertexSymmetricScatteringBoundaryBound c) / 2) ∈
          nhds 0 := Iio_mem_nhds (by linarith)
    filter_upwards [hjac.eventually hopen] with N hN
    change sixVertexSymmetricJacobianTotalErrorOfLower c N (rhoLower / 2) < _ at hN
    linarith
  filter_upwards [herrEventually, hjacEventually] with N hE hJ
  exact ⟨hE.le, hJ⟩

end

end StatMech.FrontierD
