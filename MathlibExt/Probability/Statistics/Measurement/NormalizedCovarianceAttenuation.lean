/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.LinearModel.ErrorsInVariables
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.Moments.Variance

/-!
# Signed normalized-covariance attenuation

With uncorrelated true/error, own error, and cross terms, the observed
normalized covariance is the true-score normalized covariance times the
square root of the product of the two reliabilities. This is the
correction-for-attenuation identity of classical test theory: Spearman,
"The proof and measurement of association between two things", American
Journal of Psychology 15 (1904), 72-101, where the correction
`r_true = r_obs / sqrt (rhoX * rhoY)` is introduced; rearranged, the
observed correlation is the true-score correlation attenuated by
`sqrt (rhoX * rhoY)`. Assumption map for this theorem: the observed
scores split as `X = Tx + Ex`, `Y = Ty + Ey`; `cov[Tx, Ex] = 0` and
`cov[Ty, Ey] = 0` give `Var[X] = Var[Tx] + Var[Ex]` and
`Var[Y] = Var[Ty] + Var[Ey]`, so `rhoX = attenuationFactor Var[Tx]
Var[Ex]` is the usual reliability `Var[Tx] / Var[X]`; `cov[Ex, Ey] = 0`,
`cov[Tx, Ey] = 0`, and `cov[Ex, Ty] = 0` give
`cov[X, Y] = cov[Tx, Ty]`; positivity of the four variances keeps every
square root and division nonzero.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.Measurement

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.Statistics.LinearModel.ErrorsInVariables
open scoped ProbabilityTheory

/-- **Signed normalized-covariance attenuation** (leaf F12-L-ATTEN-EQ).

Let `X = Tx + Ex` and `Y = Ty + Ey` on a probability space, with all of
`Tx`, `Ty`, `Ex`, `Ey` square integrable. Assume the true-score variances
`Var[Tx]`, `Var[Ty]` are positive (the observed variances are then
positive, since each is a true variance plus a nonnegative error
variance), the own true/error covariances `cov[Tx, Ex]`, `cov[Ty, Ey]`
vanish, the error covariance `cov[Ex, Ey]` vanishes, and the cross
true/error covariances `cov[Tx, Ey]`, `cov[Ex, Ty]` vanish. Then the
normalized covariance of the observed scores is the normalized covariance
of the true scores times `sqrt (rhoX * rhoY)`, where
`rhoX = attenuationFactor Var[Tx] Var[Ex]` and
`rhoY = attenuationFactor Var[Ty] Var[Ey]` are the reliabilities. -/
theorem normalizedCovariance_attenuation {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Tx Ty Ex Ey X Y : Ω → ℝ}
    (hX : X = fun ω => Tx ω + Ex ω) (hY : Y = fun ω => Ty ω + Ey ω)
    (hTx : MemLp Tx 2 μ) (hTy : MemLp Ty 2 μ)
    (hEx : MemLp Ex 2 μ) (hEy : MemLp Ey 2 μ)
    (hVarTx : 0 < Var[Tx; μ]) (hVarTy : 0 < Var[Ty; μ])
    (hTxEx : cov[Tx, Ex; μ] = 0) (hTyEy : cov[Ty, Ey; μ] = 0)
    (hExEy : cov[Ex, Ey; μ] = 0)
    (hTxEy : cov[Tx, Ey; μ] = 0) (hExTy : cov[Ex, Ty; μ] = 0) :
    cov[X, Y; μ] / (Real.sqrt Var[X; μ] * Real.sqrt Var[Y; μ]) =
      cov[Tx, Ty; μ] / (Real.sqrt Var[Tx; μ] * Real.sqrt Var[Ty; μ]) *
        Real.sqrt (attenuationFactor Var[Tx; μ] Var[Ex; μ] *
          attenuationFactor Var[Ty; μ] Var[Ey; μ]) := by
  have hXX : X = Tx + Ex := hX
  have hYY : Y = Ty + Ey := hY
  have hCovXY : cov[X, Y; μ] = cov[Tx, Ty; μ] := by
    rw [hXX, hYY, covariance_add_left hTx hEx (hTy.add hEy),
      covariance_add_right hTx hTy hEy, covariance_add_right hEx hTy hEy,
      hTxEy, hExTy, hExEy, add_zero, add_zero, add_zero]
  have hVarX' : Var[X; μ] = Var[Tx; μ] + Var[Ex; μ] := by
    rw [hX, variance_fun_add hTx hEx, hTxEx]
    ring
  have hVarY' : Var[Y; μ] = Var[Ty; μ] + Var[Ey; μ] := by
    rw [hY, variance_fun_add hTy hEy, hTyEy]
    ring
  have hposX : 0 < Var[Tx; μ] + Var[Ex; μ] :=
    add_pos_of_pos_of_nonneg hVarTx (variance_nonneg Ex μ)
  have hposY : 0 < Var[Ty; μ] + Var[Ey; μ] :=
    add_pos_of_pos_of_nonneg hVarTy (variance_nonneg Ey μ)
  rw [hCovXY, hVarX', hVarY']
  unfold attenuationFactor
  rw [Real.sqrt_mul (div_nonneg hVarTx.le hposX.le),
    Real.sqrt_div hVarTx.le, Real.sqrt_div hVarTy.le]
  have n1 : Real.sqrt Var[Tx; μ] ≠ 0 := (Real.sqrt_pos.mpr hVarTx).ne'
  have n2 : Real.sqrt Var[Ty; μ] ≠ 0 := (Real.sqrt_pos.mpr hVarTy).ne'
  have n3 : Real.sqrt (Var[Tx; μ] + Var[Ex; μ]) ≠ 0 :=
    (Real.sqrt_pos.mpr hposX).ne'
  have n4 : Real.sqrt (Var[Ty; μ] + Var[Ey; μ]) ≠ 0 :=
    (Real.sqrt_pos.mpr hposY).ne'
  have m1 : Real.sqrt Var[Tx; μ] * Real.sqrt Var[Ty; μ] ≠ 0 :=
    mul_ne_zero n1 n2
  have m2 : Real.sqrt (Var[Tx; μ] + Var[Ex; μ]) *
      Real.sqrt (Var[Ty; μ] + Var[Ey; μ]) ≠ 0 := mul_ne_zero n3 n4
  field_simp

end MathlibExt.Probability.Statistics.Measurement
