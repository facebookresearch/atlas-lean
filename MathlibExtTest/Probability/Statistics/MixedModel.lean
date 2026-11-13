/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MixedModel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Mixed-model tests

Concrete checks for the mixed-model response laws: zero-matrix PSD
(proved, not assumed), small `phenCov` computation, zero-mean regression,
and nonzero fixed effects exercising the mean theorems.

Clause mapping (S15.1): `Y = X β + Z b + ε` with independent centered
Gaussian `b`, `ε`; PSD `G`, PD `R` give `E[Y] = X β`,
`Cov(Y) = Z G Zᵀ + R`. Mean laws witnessed by nonzero tests; covariance
and PSD facts by zero and small-matrix tests.
-/

open MeasureTheory ProbabilityTheory Matrix MetaMathlibExt
open MathlibExt.Biology.StatisticalGenetics.MixedModel (phenCov)

namespace MathlibExt.Probability.Statistics.MixedModel

public section

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
    (hG : G.PosSemidef) (hR : R.PosDef)
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
    (hG : G.PosSemidef) (hR : R.PosDef)
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

end

end MathlibExt.Probability.Statistics.MixedModel
