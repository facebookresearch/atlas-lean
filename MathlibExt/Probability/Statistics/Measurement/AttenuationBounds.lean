/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.CovarianceBounds
public import MathlibExt.Probability.Statistics.Measurement.NormalizedCovarianceAttenuation
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.Moments.Variance

/-!
# Absolute attenuation bounds

The observed normalized covariance is bounded in absolute value both by
the square root of the product of the two reliabilities and by the
absolute true-score normalized covariance. Both bounds follow from the
signed attenuation equality together with the rescaled covariance
inequality `two_mul_abs_covariance_le`; no new correlation definition is
introduced.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.Measurement

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.Statistics.LinearModel.ErrorsInVariables
open scoped ProbabilityTheory

/-! ## Rescaling helpers (used only below; not part of the pin) -/

/-- Rescaling by the square root of its own variance preserves square-integrability. -/
private theorem memLp_div_sqrt_variance_self {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {Z : Ω → ℝ} (hZ : MemLp Z 2 μ) :
    MemLp (fun ω => Z ω / Real.sqrt Var[Z; μ]) 2 μ := by
  have h := hZ.mul_const (Real.sqrt Var[Z; μ])⁻¹
  simpa [div_eq_mul_inv] using h

/-- Rescaling by the square root of its own positive variance gives variance `1`. -/
private theorem variance_div_sqrt_variance_self {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {Z : Ω → ℝ} (hVar : 0 < Var[Z; μ]) :
    Var[fun ω => Z ω / Real.sqrt Var[Z; μ]; μ] = 1 := by
  have hne : Var[Z; μ] ≠ 0 := ne_of_gt hVar
  have hsq : (Real.sqrt Var[Z; μ]) ^ 2 = Var[Z; μ] := Real.sq_sqrt (le_of_lt hVar)
  simp only [div_eq_mul_inv]
  rw [variance_mul_const, inv_pow, hsq, mul_inv_cancel₀ hne]

/-- The covariance of the rescaled variables is the normalized covariance. -/
private theorem covariance_div_sqrt_variance {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {Z W : Ω → ℝ} :
    cov[fun ω => Z ω / Real.sqrt Var[Z; μ], fun ω => W ω / Real.sqrt Var[W; μ]; μ]
      = cov[Z, W; μ] / (Real.sqrt Var[Z; μ] * Real.sqrt Var[W; μ]) := by
  rw [covariance_fun_div_left, covariance_fun_div_right, div_div]
  congr 1
  ring

/-- The normalized covariance of two positive-variance variables is at most `1` in
absolute value, by rescaling `two_mul_abs_covariance_le`. -/
private theorem abs_cov_div_sqrt_mul_sqrt_le_one {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z W : Ω → ℝ}
    (hZ : MemLp Z 2 μ) (hW : MemLp W 2 μ)
    (hVarZ : 0 < Var[Z; μ]) (hVarW : 0 < Var[W; μ]) :
    |cov[Z, W; μ] / (Real.sqrt Var[Z; μ] * Real.sqrt Var[W; μ])| ≤ 1 := by
  have hU : MemLp (fun ω => Z ω / Real.sqrt Var[Z; μ]) 2 μ :=
    memLp_div_sqrt_variance_self hZ
  have hV : MemLp (fun ω => W ω / Real.sqrt Var[W; μ]) 2 μ :=
    memLp_div_sqrt_variance_self hW
  have h2 := MathlibExt.Probability.Statistics.two_mul_abs_covariance_le
    hU hV
  rw [covariance_div_sqrt_variance, variance_div_sqrt_variance_self hVarZ,
    variance_div_sqrt_variance_self hVarW] at h2
  linarith

/-- The reliability `s / (s + t)` lies in `[0, 1]` for positive `s` and nonnegative `t`. -/
private theorem attenuationFactor_mem_Icc {s t : ℝ} (hs : 0 < s) (ht : 0 ≤ t) :
    0 ≤ attenuationFactor s t ∧ attenuationFactor s t ≤ 1 := by
  have hpos : 0 < s + t := by linarith
  constructor
  · show 0 ≤ s / (s + t)
    exact div_nonneg (le_of_lt hs) (le_of_lt hpos)
  · show s / (s + t) ≤ 1
    rw [div_le_one hpos]
    linarith

/-! ## The bound -/

/-- **Absolute attenuation bounds**.

Under exactly the hypotheses of `normalizedCovariance_attenuation`
(decomposition `X = Tx + Ex`, `Y = Ty + Ey`, square integrability,
positive true-score variances -- the observed variances are then
positive -- and the five vanishing covariances), writing
`NCov(U, V) = cov[U, V] / (sqrt Var[U] * sqrt Var[V])` for the explicit
normalized-covariance expression (notation only; no new correlation
definition), the observed normalized covariance satisfies both
attenuation bounds
`|NCov(X, Y)| <= sqrt (rhoX * rhoY)` and
`|NCov(X, Y)| <= |NCov(Tx, Ty)|`,
where `rhoX = attenuationFactor Var[Tx] Var[Ex]` and
`rhoY = attenuationFactor Var[Ty] Var[Ey]` are the reliabilities.
Both bounds are absolute: no signed comparison between `NCov(X, Y)`
and `NCov(Tx, Ty)` is asserted, since it is false for negative
covariance without a sign premise.  Zero variance is excluded only for
the true and observed scores; either error may have zero variance,
which gives that score reliability one. -/
theorem abs_normalizedCovariance_le_attenuation {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Tx Ty Ex Ey X Y : Ω → ℝ}
    (hX : X = fun ω => Tx ω + Ex ω) (hY : Y = fun ω => Ty ω + Ey ω)
    (hTx : MemLp Tx 2 μ) (hTy : MemLp Ty 2 μ)
    (hEx : MemLp Ex 2 μ) (hEy : MemLp Ey 2 μ)
    (hVarTx : 0 < Var[Tx; μ]) (hVarTy : 0 < Var[Ty; μ])
    (hTxEx : cov[Tx, Ex; μ] = 0) (hTyEy : cov[Ty, Ey; μ] = 0)
    (hExEy : cov[Ex, Ey; μ] = 0)
    (hTxEy : cov[Tx, Ey; μ] = 0) (hExTy : cov[Ex, Ty; μ] = 0) :
    |cov[X, Y; μ] / (Real.sqrt Var[X; μ] * Real.sqrt Var[Y; μ])| ≤
        Real.sqrt (attenuationFactor Var[Tx; μ] Var[Ex; μ] *
          attenuationFactor Var[Ty; μ] Var[Ey; μ]) ∧
      |cov[X, Y; μ] / (Real.sqrt Var[X; μ] * Real.sqrt Var[Y; μ])| ≤
        |cov[Tx, Ty; μ] / (Real.sqrt Var[Tx; μ] * Real.sqrt Var[Ty; μ])| := by
  have hEq := normalizedCovariance_attenuation hX hY hTx hTy hEx hEy hVarTx hVarTy
    hTxEx hTyEy hExEy hTxEy hExTy
  obtain ⟨hrX0, hrX1⟩ :=
    attenuationFactor_mem_Icc hVarTx (variance_nonneg Ex μ)
  obtain ⟨hrY0, hrY1⟩ :=
    attenuationFactor_mem_Icc hVarTy (variance_nonneg Ey μ)
  have hrr1 : attenuationFactor Var[Tx; μ] Var[Ex; μ] *
      attenuationFactor Var[Ty; μ] Var[Ey; μ] ≤ 1 :=
    calc attenuationFactor Var[Tx; μ] Var[Ex; μ] *
          attenuationFactor Var[Ty; μ] Var[Ey; μ]
        ≤ 1 * attenuationFactor Var[Ty; μ] Var[Ey; μ] :=
          mul_le_mul_of_nonneg_right hrX1 hrY0
      _ = attenuationFactor Var[Ty; μ] Var[Ey; μ] := one_mul _
      _ ≤ 1 := hrY1
  have hs0 : 0 ≤ Real.sqrt (attenuationFactor Var[Tx; μ] Var[Ex; μ] *
      attenuationFactor Var[Ty; μ] Var[Ey; μ]) := Real.sqrt_nonneg _
  have hs1 : Real.sqrt (attenuationFactor Var[Tx; μ] Var[Ex; μ] *
      attenuationFactor Var[Ty; μ] Var[Ey; μ]) ≤ 1 := by
    have h := Real.sqrt_le_sqrt hrr1
    rwa [Real.sqrt_one] at h
  have hNT1 : |cov[Tx, Ty; μ] / (Real.sqrt Var[Tx; μ] * Real.sqrt Var[Ty; μ])| ≤ 1 :=
    abs_cov_div_sqrt_mul_sqrt_le_one hTx hTy hVarTx hVarTy
  have habs : |cov[X, Y; μ] / (Real.sqrt Var[X; μ] * Real.sqrt Var[Y; μ])|
      = |cov[Tx, Ty; μ] / (Real.sqrt Var[Tx; μ] * Real.sqrt Var[Ty; μ])| *
        Real.sqrt (attenuationFactor Var[Tx; μ] Var[Ex; μ] *
          attenuationFactor Var[Ty; μ] Var[Ey; μ]) := by
    rw [hEq, abs_mul, abs_of_nonneg hs0]
  rw [habs]
  constructor
  · calc |cov[Tx, Ty; μ] / (Real.sqrt Var[Tx; μ] * Real.sqrt Var[Ty; μ])| *
          Real.sqrt (attenuationFactor Var[Tx; μ] Var[Ex; μ] *
            attenuationFactor Var[Ty; μ] Var[Ey; μ])
        ≤ 1 * Real.sqrt (attenuationFactor Var[Tx; μ] Var[Ex; μ] *
            attenuationFactor Var[Ty; μ] Var[Ey; μ]) :=
          mul_le_mul_of_nonneg_right hNT1 hs0
      _ = Real.sqrt (attenuationFactor Var[Tx; μ] Var[Ex; μ] *
          attenuationFactor Var[Ty; μ] Var[Ey; μ]) := one_mul _
  · calc |cov[Tx, Ty; μ] / (Real.sqrt Var[Tx; μ] * Real.sqrt Var[Ty; μ])| *
          Real.sqrt (attenuationFactor Var[Tx; μ] Var[Ex; μ] *
            attenuationFactor Var[Ty; μ] Var[Ey; μ])
        ≤ |cov[Tx, Ty; μ] / (Real.sqrt Var[Tx; μ] * Real.sqrt Var[Ty; μ])| * 1 :=
          mul_le_mul_of_nonneg_left hs1 (abs_nonneg _)
      _ = |cov[Tx, Ty; μ] / (Real.sqrt Var[Tx; μ] * Real.sqrt Var[Ty; μ])| :=
          mul_one _
end MathlibExt.Probability.Statistics.Measurement
