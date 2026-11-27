/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ClassNumberBernoulliEulerCongruenceEisensteinRealPeriodEqBetaGamma
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Tests for the Beta and Gamma values of the real Eisenstein period

Positivity of the real period `∫ t in (0 : ℝ)..1, (1 - t ^ 3) ^ (-(2 / 3) : ℝ)`,
the induced relation between the Beta values `B(1/3, 1/3)` and `B(1/6, 1/2)`,
and the cubed Gamma value `Real.Gamma (1 / 3) ^ 3` in terms of the period.
-/

@[expose] public section

namespace MathlibExtTest.NumberTheory.ClassNumberBernoulliEulerCongruenceEisensteinRealPeriodEqBetaGamma

/-- The real Eisenstein period is positive, by its Gamma-value formula. -/
theorem eisensteinRealPeriod_pos :
    0 < ∫ t in (0 : ℝ)..1, (1 - t ^ 3) ^ (-(2 / 3) : ℝ) := by
  obtain ⟨-, hGamma, -⟩ := MetaMathlibExt.eisensteinRealPeriod_eq_beta_gamma
  have hG : 0 < Real.Gamma (1 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  have hpi : 0 < Real.pi := Real.pi_pos
  have hs3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  rw [hGamma]
  positivity

/-- The two Beta-value formulas for the period give a relation between
`B(1/3, 1/3)` and `B(1/6, 1/2)`. -/
theorem betaIntegral_third_eq_sixth_half :
    Complex.betaIntegral (1 / 3) (1 / 3) / 3
      = (((2 : ℝ) ^ (1 / 3 : ℝ) / (3 * Real.sqrt 3) : ℝ) : ℂ) *
        Complex.betaIntegral (1 / 6) (1 / 2) := by
  obtain ⟨hbeta, -, hbeta'⟩ := MetaMathlibExt.eisensteinRealPeriod_eq_beta_gamma
  rw [← hbeta]
  exact hbeta'

/-- The cubed Gamma value at `1 / 3` in terms of the real period. -/
theorem gamma_third_cubed :
    Real.Gamma (1 / 3) ^ 3
      = (∫ t in (0 : ℝ)..1, (1 - t ^ 3) ^ (-(2 / 3) : ℝ)) *
        (2 * Real.pi * Real.sqrt 3) := by
  obtain ⟨-, hGamma, -⟩ := MetaMathlibExt.eisensteinRealPeriod_eq_beta_gamma
  have hG : 0 < Real.Gamma (1 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  have hpi : 0 < Real.pi := Real.pi_pos
  have hs3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hD : (2 * Real.pi * Real.sqrt 3) ≠ 0 := by positivity
  rw [hGamma]
  exact (div_mul_cancel₀ _ hD).symm

end MathlibExtTest.NumberTheory.ClassNumberBernoulliEulerCongruenceEisensteinRealPeriodEqBetaGamma
