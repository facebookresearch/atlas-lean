/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Measurement.NormalizedCovarianceAttenuation

/-!
# Normalized-covariance attenuation tests

A signed Rademacher-style moment instance, and the hypothesis-failure form
for nonorthogonal errors.
-/

@[expose] public section

namespace MathlibExtTest.Probability.Statistics.Measurement

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.Statistics.Measurement
open MathlibExt.Probability.Statistics.LinearModel.ErrorsInVariables
open scoped ProbabilityTheory

/-- Rademacher-style sign instance, as an implication over concrete
covariance/variance values: perfectly negatively associated true scores
(unit variances, covariance `-1`, latent normalized covariance `-1`) with
unit-variance uncorrelated errors give observed variances `2`, observed
covariance `-1`, hence observed normalized covariance `-1/2`, matching the
attenuation factor `sqrt ((1/2) * (1/2)) = 1/2`. No Rademacher variable is
constructed; the moment values are the hypotheses. -/
theorem normalizedCovariance_attenuation_rademacher {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Tx Ty Ex Ey X Y : Ω → ℝ}
    (hCovT : cov[Tx, Ty; μ] = -1)
    (hVarTx : Var[Tx; μ] = 1) (hVarTy : Var[Ty; μ] = 1)
    (hCov : cov[X, Y; μ] = -1)
    (hVarX : Var[X; μ] = 2) (hVarY : Var[Y; μ] = 2)
    (hVarEx : Var[Ex; μ] = 1) (hVarEy : Var[Ey; μ] = 1) :
    cov[Tx, Ty; μ] / (Real.sqrt Var[Tx; μ] * Real.sqrt Var[Ty; μ]) = -1 ∧
      cov[X, Y; μ] / (Real.sqrt Var[X; μ] * Real.sqrt Var[Y; μ]) = -1 / 2 ∧
      cov[X, Y; μ] / (Real.sqrt Var[X; μ] * Real.sqrt Var[Y; μ]) =
        cov[Tx, Ty; μ] / (Real.sqrt Var[Tx; μ] * Real.sqrt Var[Ty; μ]) *
          Real.sqrt (attenuationFactor Var[Tx; μ] Var[Ex; μ] *
            attenuationFactor Var[Ty; μ] Var[Ey; μ]) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hCovT, hVarTx, hVarTy, Real.sqrt_one, mul_one, div_one]
  · rw [hCov, hVarX, hVarY,
      Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · rw [hCov, hVarX, hVarY, hCovT, hVarTx, hVarTy, hVarEx, hVarEy]
    unfold attenuationFactor
    rw [Real.sqrt_one, mul_one, div_one]
    have h2 : ((1 : ℝ) / (1 + 1)) * (1 / (1 + 1)) = 1 / 4 := by norm_num
    rw [h2, show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num,
      Real.sqrt_sq (show (0 : ℝ) ≤ 1 / 2 by norm_num),
      Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    ring

/-- Nonorthogonal errors break a premise of
`normalizedCovariance_attenuation`: if `cov[Ex, Ey] ≠ 0`, the five
zero-covariance premises cannot all hold. This is the hypothesis-failure
form; it does not assert that the conclusion fails. -/
theorem nonorthogonal_errors_break_premise {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Tx Ty Ex Ey : Ω → ℝ} (hExEy : cov[Ex, Ey; μ] ≠ 0) :
    ¬ (cov[Tx, Ex; μ] = 0 ∧ cov[Ty, Ey; μ] = 0 ∧ cov[Ex, Ey; μ] = 0 ∧
      cov[Tx, Ey; μ] = 0 ∧ cov[Ex, Ty; μ] = 0) := by
  rintro ⟨_, _, h, _, _⟩
  exact hExEy h

/-- The production theorem applied to the signed moment instance:
supplying the decomposition, integrability, positivity, and five
zero-covariance hypotheses of `normalizedCovariance_attenuation`, the
observed normalized covariance for the `-1` true covariance instance is
`-1 / 2`. -/
theorem normalizedCovariance_attenuation_applied {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Tx Ty Ex Ey X Y : Ω → ℝ}
    (hX : X = fun ω => Tx ω + Ex ω) (hY : Y = fun ω => Ty ω + Ey ω)
    (hTx : MemLp Tx 2 μ) (hTy : MemLp Ty 2 μ)
    (hEx : MemLp Ex 2 μ) (hEy : MemLp Ey 2 μ)
    (hVarTx : Var[Tx; μ] = 1) (hVarTy : Var[Ty; μ] = 1)
    (hVarX : Var[X; μ] = 2) (hVarY : Var[Y; μ] = 2)
    (hVarEx : Var[Ex; μ] = 1) (hVarEy : Var[Ey; μ] = 1)
    (hCovT : cov[Tx, Ty; μ] = -1)
    (hTxEx : cov[Tx, Ex; μ] = 0) (hTyEy : cov[Ty, Ey; μ] = 0)
    (hExEy : cov[Ex, Ey; μ] = 0)
    (hTxEy : cov[Tx, Ey; μ] = 0) (hExTy : cov[Ex, Ty; μ] = 0) :
    cov[X, Y; μ] / (Real.sqrt Var[X; μ] * Real.sqrt Var[Y; μ]) = -1 / 2 := by
  have h := normalizedCovariance_attenuation hX hY hTx hTy hEx hEy
    (by rw [hVarTx]; norm_num) (by rw [hVarTy]; norm_num)
    hTxEx hTyEy hExEy hTxEy hExTy
  rw [hCovT, hVarTx, hVarTy, hVarEx, hVarEy] at h
  rw [h, Real.sqrt_one, mul_one, div_one]
  unfold MathlibExt.Probability.Statistics.LinearModel.ErrorsInVariables.attenuationFactor
  rw [show ((1 : ℝ) / (1 + 1)) * (1 / (1 + 1)) = 1 / 4 by norm_num,
    show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num,
    Real.sqrt_sq (show (0 : ℝ) ≤ 1 / 2 by norm_num)]
  norm_num

end MathlibExtTest.Probability.Statistics.Measurement
