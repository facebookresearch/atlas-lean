/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Measurement.AttenuationBounds

/-!
# Absolute attenuation bound tests

Negative, positive, and zero covariance moment instances.
-/

@[expose] public section

namespace MathlibExtTest.Probability.Statistics.Measurement

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.Statistics.Measurement
open MathlibExt.Probability.Statistics.LinearModel.ErrorsInVariables
open scoped ProbabilityTheory

open MathlibExt.Probability.Statistics.Measurement
open MathlibExt.Probability.Statistics.LinearModel.ErrorsInVariables

/-- Negative covariance: unit-variance true scores with covariance `-1`
(latent normalized covariance `-1`) and unit-variance errors give
observed normalized covariance `-1 / 2`; the first bound is an equality
(`sqrt ((1/2) * (1/2)) = 1 / 2`) and the second is `-1 / 2` against
`|-1| = 1` in absolute value. -/
theorem abs_normalizedCovariance_le_attenuation_negative {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Tx Ty Ex Ey X Y : Ω → ℝ}
    (hCovT : cov[Tx, Ty; μ] = -1)
    (hVarTx : Var[Tx; μ] = 1) (hVarTy : Var[Ty; μ] = 1)
    (hCov : cov[X, Y; μ] = -1)
    (hVarX : Var[X; μ] = 2) (hVarY : Var[Y; μ] = 2)
    (hVarEx : Var[Ex; μ] = 1) (hVarEy : Var[Ey; μ] = 1) :
    |cov[X, Y; μ] / (Real.sqrt Var[X; μ] * Real.sqrt Var[Y; μ])| ≤
        Real.sqrt (attenuationFactor Var[Tx; μ] Var[Ex; μ] *
          attenuationFactor Var[Ty; μ] Var[Ey; μ]) ∧
      |cov[X, Y; μ] / (Real.sqrt Var[X; μ] * Real.sqrt Var[Y; μ])| ≤
        |cov[Tx, Ty; μ] / (Real.sqrt Var[Tx; μ] * Real.sqrt Var[Ty; μ])| ∧
      cov[X, Y; μ] / (Real.sqrt Var[X; μ] * Real.sqrt Var[Y; μ]) = -1 / 2 := by
  rw [hCovT, hVarTx, hVarTy, hCov, hVarX, hVarY, hVarEx, hVarEy]
  have h22 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h12 : attenuationFactor (1 : ℝ) (1 : ℝ) = 1 / 2 := by
    unfold attenuationFactor
    norm_num
  have hrho : Real.sqrt (attenuationFactor (1 : ℝ) 1 * attenuationFactor 1 1)
      = 1 / 2 := by
    rw [h12, show (1 / 2 : ℝ) * (1 / 2) = (1 / 2) ^ 2 by ring,
      Real.sqrt_sq (by norm_num)]
  rw [Real.sqrt_one, h22, hrho]
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

/-- Positive covariance: `Var[Tx] = 1`, `Var[Ty] = 4`, covariance `1`
(latent normalized covariance `1 / 2`), error variances `1` and `4`,
give reliabilities `1 / 2, 1 / 2` and observed normalized covariance
`1 / 4`, strictly below both bounds `1 / 2`. -/
theorem abs_normalizedCovariance_le_attenuation_positive {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Tx Ty Ex Ey X Y : Ω → ℝ}
    (hCovT : cov[Tx, Ty; μ] = 1)
    (hVarTx : Var[Tx; μ] = 1) (hVarTy : Var[Ty; μ] = 4)
    (hCov : cov[X, Y; μ] = 1)
    (hVarX : Var[X; μ] = 2) (hVarY : Var[Y; μ] = 8)
    (hVarEx : Var[Ex; μ] = 1) (hVarEy : Var[Ey; μ] = 4) :
    |cov[X, Y; μ] / (Real.sqrt Var[X; μ] * Real.sqrt Var[Y; μ])| ≤
        Real.sqrt (attenuationFactor Var[Tx; μ] Var[Ex; μ] *
          attenuationFactor Var[Ty; μ] Var[Ey; μ]) ∧
      |cov[X, Y; μ] / (Real.sqrt Var[X; μ] * Real.sqrt Var[Y; μ])| ≤
        |cov[Tx, Ty; μ] / (Real.sqrt Var[Tx; μ] * Real.sqrt Var[Ty; μ])| ∧
      cov[X, Y; μ] / (Real.sqrt Var[X; μ] * Real.sqrt Var[Y; μ]) = 1 / 4 := by
  rw [hCovT, hVarTx, hVarTy, hCov, hVarX, hVarY, hVarEx, hVarEy]
  have h28 : Real.sqrt 2 * Real.sqrt 8 = 4 := by
    have hmul := Real.sqrt_mul (show (0 : ℝ) ≤ 2 by norm_num) (8 : ℝ)
    have h16 : Real.sqrt (16 : ℝ) = 4 := by
      have h162 : (16 : ℝ) = 4 ^ 2 := by norm_num
      rw [h162]
      exact Real.sqrt_sq (by norm_num)
    have h28' : (2 : ℝ) * 8 = 16 := by norm_num
    rw [h28'] at hmul
    rw [h16] at hmul
    exact hmul.symm
  have h4 : Real.sqrt (4 : ℝ) = 2 := by
    have h42 : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [h42]
    exact Real.sqrt_sq (by norm_num)
  have h12 : attenuationFactor (1 : ℝ) (1 : ℝ) = 1 / 2 := by
    unfold attenuationFactor
    norm_num
  have h44 : attenuationFactor (4 : ℝ) (4 : ℝ) = 1 / 2 := by
    unfold attenuationFactor
    norm_num
  have hrho : Real.sqrt (attenuationFactor (1 : ℝ) 1 * attenuationFactor 4 4)
      = 1 / 2 := by
    rw [h12, h44, show (1 / 2 : ℝ) * (1 / 2) = (1 / 2) ^ 2 by ring,
      Real.sqrt_sq (by norm_num)]
  rw [Real.sqrt_one, h4, h28, hrho]
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

/-- Zero covariance: uncorrelated true scores (variances `1, 1`,
covariance `0`) with unit-variance errors give observed normalized
covariance `0`; the second bound is an equality (`0 <= |0|`). -/
theorem abs_normalizedCovariance_le_attenuation_zero {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Tx Ty Ex Ey X Y : Ω → ℝ}
    (hCovT : cov[Tx, Ty; μ] = 0)
    (hVarTx : Var[Tx; μ] = 1) (hVarTy : Var[Ty; μ] = 1)
    (hCov : cov[X, Y; μ] = 0)
    (hVarX : Var[X; μ] = 2) (hVarY : Var[Y; μ] = 2)
    (hVarEx : Var[Ex; μ] = 1) (hVarEy : Var[Ey; μ] = 1) :
    |cov[X, Y; μ] / (Real.sqrt Var[X; μ] * Real.sqrt Var[Y; μ])| ≤
        Real.sqrt (attenuationFactor Var[Tx; μ] Var[Ex; μ] *
          attenuationFactor Var[Ty; μ] Var[Ey; μ]) ∧
      |cov[X, Y; μ] / (Real.sqrt Var[X; μ] * Real.sqrt Var[Y; μ])| ≤
        |cov[Tx, Ty; μ] / (Real.sqrt Var[Tx; μ] * Real.sqrt Var[Ty; μ])| ∧
      cov[X, Y; μ] / (Real.sqrt Var[X; μ] * Real.sqrt Var[Y; μ]) = 0 := by
  rw [hCovT, hVarTx, hVarTy, hCov, hVarX, hVarY, hVarEx, hVarEy]
  have h0 : (0 : ℝ) / (Real.sqrt 2 * Real.sqrt 2) = 0 := zero_div _
  refine ⟨?_, ?_, ?_⟩
  · rw [h0, abs_zero]
    exact Real.sqrt_nonneg _
  · rw [h0, abs_zero]
    exact abs_nonneg _
  · exact h0


/-- Applied instance: the production theorem is invoked with an actual
true/error decomposition and its zero-covariance hypotheses, at the
moment values of the negative test. -/
theorem abs_normalizedCovariance_le_attenuation_applied {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Tx Ty Ex Ey X Y : Ω → ℝ}
    (hX : X = fun ω => Tx ω + Ex ω) (hY : Y = fun ω => Ty ω + Ey ω)
    (hTx : MemLp Tx 2 μ) (hTy : MemLp Ty 2 μ)
    (hEx : MemLp Ex 2 μ) (hEy : MemLp Ey 2 μ)
    (hVarTx : Var[Tx; μ] = 1) (hVarTy : Var[Ty; μ] = 1)
    (hVarEx : Var[Ex; μ] = 1) (hVarEy : Var[Ey; μ] = 1)
    (hCov : cov[X, Y; μ] = -1) (hCovT : cov[Tx, Ty; μ] = -1)
    (hVarX : Var[X; μ] = 2) (hVarY : Var[Y; μ] = 2)
    (hTxEx : cov[Tx, Ex; μ] = 0) (hTyEy : cov[Ty, Ey; μ] = 0)
    (hExEy : cov[Ex, Ey; μ] = 0)
    (hTxEy : cov[Tx, Ey; μ] = 0) (hExTy : cov[Ex, Ty; μ] = 0) :
    |cov[X, Y; μ] / (Real.sqrt Var[X; μ] * Real.sqrt Var[Y; μ])| ≤ 1 / 2 ∧
      |cov[X, Y; μ] / (Real.sqrt Var[X; μ] * Real.sqrt Var[Y; μ])| ≤ 1 := by
  have h := abs_normalizedCovariance_le_attenuation hX hY hTx hTy hEx hEy
    (by rw [hVarTx]; norm_num) (by rw [hVarTy]; norm_num)
    hTxEx hTyEy hExEy hTxEy hExTy
  rw [hVarTx, hVarTy, hVarEx, hVarEy] at h
  unfold MathlibExt.Probability.Statistics.LinearModel.ErrorsInVariables.attenuationFactor at h
  rw [show ((1 : ℝ) / (1 + 1)) * (1 / (1 + 1)) = (1 / 2) ^ 2 by norm_num,
    Real.sqrt_sq (show (0 : ℝ) ≤ 1 / 2 by norm_num), hCovT] at h
  simpa using h

end MathlibExtTest.Probability.Statistics.Measurement
