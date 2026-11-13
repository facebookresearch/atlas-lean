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

/-! ### Gaussian response laws

Concrete checks for the response laws: zero-matrix PSD (proved, not assumed), a small
`phenCov` computation, zero-mean regression, nonzero fixed effects exercising the mean
theorems, a within-cluster contrast, and a singular (zero) residual covariance. -/

section GaussianResponse

open ProbabilityTheory MetaMathlibExt

/-- Zero matrix is positive semidefinite (proved here, not assumed). -/
theorem test_posSemidef_zero :
    (0 : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef := by
  exact Matrix.PosSemidef.zero

/-- Small `phenCov` computation: all-ones `Z` with zero `G` and zero `R`
gives zero. -/
theorem test_phenCov_zero_eq :
    phenCov (Matrix.of fun _ _ => (1 : ℝ))
      (0 : Matrix (Fin 1) (Fin 1) ℝ)
      (0 : Matrix (Fin 2) (Fin 2) ℝ) = 0 := by
  simp [phenCov]

/-- PSD of the small zero `phenCov`, via the production PSD theorem with
proved (not assumed) zero PSD facts. -/
theorem test_phenCov_zero_psd :
    (phenCov (Matrix.of fun _ _ => (1 : ℝ))
      (0 : Matrix (Fin 1) (Fin 1) ℝ)
      (0 : Matrix (Fin 2) (Fin 2) ℝ)).PosSemidef := by
  apply posSemidef_phenCov_of_posSemidef
  · exact Matrix.PosSemidef.zero
  · exact Matrix.PosSemidef.zero

/-- Zero-mean regression: with `X = 0` and `β = 0`, the mean is zero. -/
theorem test_integral_zero_mean {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (γ : Ω → EuclideanSpace ℝ (Fin 1))
    (ε : Ω → EuclideanSpace ℝ (Fin 2))
    (hγ : Measurable γ) (hε : Measurable ε) (hind : IndepFun γ ε P)
    (Z : Matrix (Fin 2) (Fin 1) ℝ)
    (G : Matrix (Fin 1) (Fin 1) ℝ) (R : Matrix (Fin 2) (Fin 2) ℝ)
    (hG : G.PosSemidef) (hR : R.PosSemidef)
    (hγl : P.map γ = multivariateGaussian 0 G)
    (hεl : P.map ε = multivariateGaussian 0 R) :
    ∫ ω, (toEuclideanLin (0 : Matrix (Fin 2) (Fin 1) ℝ) 0 +
      toEuclideanLin Z (γ ω) + ε ω) ∂P = 0 := by
  have h := integral_mixedModel_response γ ε hγ hε hind
    (0 : Matrix (Fin 2) (Fin 1) ℝ) (0 : EuclideanSpace ℝ (Fin 1)) Z G R hG hR
    hγl hεl
  simpa using h

/-- Nonzero fixed effects exercise the mean theorem: `X ≠ 0`, `β ≠ 0`.
E.g., `X = [[1], [2]]`, `β = [3]` gives `X β = [3, 6]` (hand computation
in the report). -/
theorem test_integral_nonzero_mean {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (γ : Ω → EuclideanSpace ℝ (Fin 1))
    (ε : Ω → EuclideanSpace ℝ (Fin 2))
    (hγ : Measurable γ) (hε : Measurable ε) (hind : IndepFun γ ε P)
    (X : Matrix (Fin 2) (Fin 1) ℝ) (β : EuclideanSpace ℝ (Fin 1))
    (hX : X ≠ 0) (hβ : β ≠ 0) (Z : Matrix (Fin 2) (Fin 1) ℝ)
    (G : Matrix (Fin 1) (Fin 1) ℝ) (R : Matrix (Fin 2) (Fin 2) ℝ)
    (hG : G.PosSemidef) (hR : R.PosSemidef)
    (hγl : P.map γ = multivariateGaussian 0 G)
    (hεl : P.map ε = multivariateGaussian 0 R) :
    ∫ ω, (toEuclideanLin X β + toEuclideanLin Z (γ ω) + ε ω) ∂P =
      toEuclideanLin X β := by
  -- `hX`/`hβ` are contract witnesses (nonzero fixed effects); the mean law
  -- itself needs no nondegeneracy.
  have _hX' := hX
  have _hβ' := hβ
  exact integral_mixedModel_response γ ε hγ hε hind X β Z G R hG hR hγl hεl

/-- Nonzero fixed effects exercise the marginal-law theorem: `X ≠ 0`,
`β ≠ 0`. Same `[[1], [2]]`, `[3]` example as above. -/
theorem test_map_nonzero_mean {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (γ : Ω → EuclideanSpace ℝ (Fin 1))
    (ε : Ω → EuclideanSpace ℝ (Fin 2))
    (hγ : Measurable γ) (hε : Measurable ε) (hind : IndepFun γ ε P)
    (X : Matrix (Fin 2) (Fin 1) ℝ) (β : EuclideanSpace ℝ (Fin 1))
    (hX : X ≠ 0) (hβ : β ≠ 0) (Z : Matrix (Fin 2) (Fin 1) ℝ)
    (G : Matrix (Fin 1) (Fin 1) ℝ) (R : Matrix (Fin 2) (Fin 2) ℝ)
    (hG : G.PosSemidef) (hR : R.PosSemidef)
    (hγl : P.map γ = multivariateGaussian 0 G)
    (hεl : P.map ε = multivariateGaussian 0 R) :
    P.map (fun ω => toEuclideanLin X β + toEuclideanLin Z (γ ω) + ε ω) =
      multivariateGaussian (toEuclideanLin X β) (phenCov Z G R) := by
  -- `hX`/`hβ` are contract witnesses (nonzero fixed effects); the marginal
  -- law itself needs no nondegeneracy.
  have _hX' := hX
  have _hβ' := hβ
  exact map_mixedModel_response γ ε hγ hε hind X β Z G R hG hR hγl hεl

/-- Closed hand computation: `X = [[1], [2]]`, `β = [3]` gives `X β = [3, 6]`. -/
theorem test_toEuclideanLin_hand :
    WithLp.ofLp (toEuclideanLin (!![1; 2] : Matrix (Fin 2) (Fin 1) ℝ)
      (WithLp.toLp 2 ![3])) = ![3, 6] := by
  have h : WithLp.ofLp (toEuclideanLin (!![1; 2] : Matrix (Fin 2) (Fin 1) ℝ)
      (WithLp.toLp 2 ![3])) =
      (!![1; 2] : Matrix (Fin 2) (Fin 1) ℝ) *ᵥ ![3] := rfl
  rw [h]
  ext i
  fin_cases i
  simp [Matrix.mulVec]
  norm_num [Matrix.of_apply]

/-- Focused check of `variance_contrast_mixedModel_response`: in one cluster of two observations
(`Z` all ones) with `G = 5 • 1` and `R = 1`, the within-cluster difference `y₀ - y₁` has
variance `2`; the shared random effect cancels. -/
theorem test_variance_contrast_within_cluster {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (γ : Ω → EuclideanSpace ℝ (Fin 1))
    (ε : Ω → EuclideanSpace ℝ (Fin 2))
    (hγ : Measurable γ) (hε : Measurable ε) (hind : IndepFun γ ε P)
    (X : Matrix (Fin 2) (Fin 1) ℝ) (β : EuclideanSpace ℝ (Fin 1))
    (hγl : P.map γ = multivariateGaussian 0 ((5 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)))
    (hεl : P.map ε = multivariateGaussian 0 (1 : Matrix (Fin 2) (Fin 2) ℝ)) :
    Var[fun ω => ∑ k, ![(1 : ℝ), -1] k * (toEuclideanLin X β +
      toEuclideanLin (Matrix.of fun _ _ => (1 : ℝ) : Matrix (Fin 2) (Fin 1) ℝ) (γ ω) +
      ε ω).ofLp k; P] = 2 := by
  rw [variance_contrast_mixedModel_response γ ε hγ hε hind X β
    (Matrix.of fun _ _ => (1 : ℝ) : Matrix (Fin 2) (Fin 1) ℝ)
    ((5 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) (1 : Matrix (Fin 2) (Fin 2) ℝ)
    (Matrix.PosSemidef.one.smul (by norm_num)) Matrix.PosSemidef.one hγl hεl ![1, -1]]
  simp [phenCov, dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.mul_apply,
    Matrix.one_apply]
  norm_num

/-- Singular residual covariance is allowed: with `R = 0` (deterministic residuals) the response
covariance is `Z G Zᵀ`. -/
theorem test_covariance_zero_residual {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (γ : Ω → EuclideanSpace ℝ (Fin 1))
    (ε : Ω → EuclideanSpace ℝ (Fin 2))
    (hγ : Measurable γ) (hε : Measurable ε) (hind : IndepFun γ ε P)
    (X : Matrix (Fin 2) (Fin 1) ℝ) (β : EuclideanSpace ℝ (Fin 1))
    (Z : Matrix (Fin 2) (Fin 1) ℝ) (G : Matrix (Fin 1) (Fin 1) ℝ) (hG : G.PosSemidef)
    (hγl : P.map γ = multivariateGaussian 0 G)
    (hεl : P.map ε = multivariateGaussian 0 (0 : Matrix (Fin 2) (Fin 2) ℝ)) (i j : Fin 2) :
    cov[fun ω => (toEuclideanLin X β + toEuclideanLin Z (γ ω) + ε ω).ofLp i,
      fun ω => (toEuclideanLin X β + toEuclideanLin Z (γ ω) + ε ω).ofLp j; P] =
      (Z * G * Zᵀ) i j := by
  rw [covariance_mixedModel_response γ ε hγ hε hind X β Z G 0 hG Matrix.PosSemidef.zero
    hγl hεl i j]
  simp [phenCov]

end GaussianResponse

end MathlibExtTest.MixedModel
