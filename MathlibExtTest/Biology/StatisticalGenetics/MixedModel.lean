/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.StatisticalGenetics.MixedModel
import Mathlib.Algebra.Order.Star.Real

/-! # Tests for `MathlibExt.Biology.StatisticalGenetics.MixedModel` -/

open Matrix MeasureTheory MathlibExt.Biology.StatisticalGenetics.LDScore
  MathlibExt.Biology.StatisticalGenetics.MixedModel

namespace MathlibExtTest.MixedModel

/-- The `1 × 1` identity matrix. -/
abbrev I1 : Matrix (Fin 1) (Fin 1) ℝ := 1

private noncomputable abbrev singletonMeasure : Measure Unit := Measure.dirac ()

private abbrev zeroEffect : Fin 1 → ℝ := 0

private def constantNoise : Fin 1 → Unit → ℝ := fun _ _ => 1

private theorem constantNoise_integrable (i i' : Fin 1) :
    Integrable (fun ω => constantNoise i ω * constantNoise i' ω) singletonMeasure := by
  simp [constantNoise]

private theorem constantNoise_secondMoment (i i' : Fin 1) :
    ∫ ω, constantNoise i ω * constantNoise i' ω ∂singletonMeasure =
      if i = i' then 1 else 0 := by
  have : i = i' := Subsingleton.elim _ _
  subst i'
  simp [constantNoise, singletonMeasure]

/-- The countermodel's noise is not mean-zero. -/
example : ∫ ω, constantNoise 0 ω ∂singletonMeasure = 1 := by
  simp [constantNoise, singletonMeasure]

/-- With `N = M = 1`, `X = 1`, `β = 0`, and constant unit noise, the raw residual-product
identity has value `1`. -/
example :
    ∫ ω, (marginalEffect I1 zeroEffect constantNoise 0 ω -
          ∑ l, ldCorr I1 0 l * zeroEffect l) *
        (marginalEffect I1 zeroEffect constantNoise 0 ω -
          ∑ l, ldCorr I1 0 l * zeroEffect l) ∂singletonMeasure = 1 := by
  simpa [I1, ldCorr] using
    (integral_marginalEffect_sub_mul (P := singletonMeasure) I1 zeroEffect
      constantNoise_integrable constantNoise_secondMoment 0 0)

/-- In the same countermodel the actual covariance of the (constant) estimator with itself is
`0`, so the raw second moment above cannot be called a covariance without a mean-zero premise. -/
example :
    ProbabilityTheory.covariance (marginalEffect I1 zeroEffect constantNoise 0)
      (marginalEffect I1 zeroEffect constantNoise 0) singletonMeasure = 0 := by
  have hconstant : marginalEffect I1 zeroEffect constantNoise 0 = fun _ : Unit => 1 := by
    funext ω
    simp [marginalEffect, I1, zeroEffect, constantNoise]
  rw [hconstant]
  exact ProbabilityTheory.covariance_const_left 1

/-- One observation `y = b + u + e` with `Var u = Var e = 1`: the mixed-model equations are
solved by `b̂ = y` and `û = 0` (the fixed effect absorbs the observation). -/
example (y : Fin 1 → ℝ) : IsMMESolution I1 I1 I1 I1 y y 0 := by
  simp [IsMMESolution]

/-- The same solution through `isMMESolution_iff_gls`: `b̂` is the GLS estimate and
`û = G Zᵀ V⁻¹ (y - X b̂) = 0`. -/
example (y : Fin 1 → ℝ) :
    y = MathlibExt.Probability.Statistics.GeneralizedLeastSquares.glsMatrix I1
      (phenCov I1 I1 I1) *ᵥ y := by
  have hX : IsUnit (I1ᵀ * (phenCov I1 I1 I1)⁻¹ * I1) := by
    simpa using (posDef_phenCov (Z := I1) Matrix.PosDef.one Matrix.PosDef.one).inv.isUnit
  have h : IsMMESolution I1 I1 I1 I1 y y 0 := by simp [IsMMESolution]
  exact ((isMMESolution_iff_gls Matrix.PosDef.one Matrix.PosDef.one hX y y 0).mp h).1

/-- With no fixed effects, the BLUP of a single random effect from one observation with
`Var u = g`, `Var e = r` is the shrinkage estimate `g / (g + r) · y`. -/
example {g r : ℝ} (hg : 0 < g) (hr : 0 < r) (y : Fin 1 → ℝ) :
    ((g • I1) * I1ᵀ * (phenCov I1 (g • I1) (r • I1))⁻¹) *ᵥ y = (g / (g + r)) • y := by
  have hV : phenCov I1 (g • I1) (r • I1) = (g + r) • I1 := by
    simp [phenCov, add_smul]
  have hgr : g + r ≠ 0 := by positivity
  have hinv : ((g + r) • I1)⁻¹ = (g + r)⁻¹ • I1 :=
    Matrix.inv_eq_left_inv (by simp [smul_smul, mul_inv_cancel₀ hgr])
  rw [hV, hinv]
  ext i; fin_cases i; simp [Matrix.mulVec, dotProduct]
  field_simp
  simp

/-- With no samples the marginal estimate is the junk value `0` (`x / 0 = 0`). -/
example {Ω : Type*} (X : Matrix (Fin 0) (Fin 1) ℝ) (β : Fin 1 → ℝ) (ε : Fin 0 → Ω → ℝ)
    (ω : Ω) : marginalEffect X β ε 0 ω = 0 := by
  simp [marginalEffect]

end MathlibExtTest.MixedModel
