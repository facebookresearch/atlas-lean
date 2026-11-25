/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.TalagrandTransport
import MathlibExt.InformationTheory.ScalarGaussianKL
import Mathlib.Probability.Distributions.Gaussian.Fernique

/-! # Tests for `MathlibExt.Probability.TalagrandTransport` -/

namespace MathlibExtTest.TalagrandTransport

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

open MathlibExt.MeasureTheory.OptimalTransport.Wasserstein (wasserstein wasserstein_mono)
open MathlibExt.Probability.TalagrandTransportWanted (talagrand_stdGaussian)

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

-- The square-root form `W₂(μ, γ) ≤ √(2 KL(μ ‖ γ))` of Villani's `T₂(1)`.
example (μ : ProbabilityMeasure E) (hμ : ∫⁻ x, ‖x‖ₑ ^ (2 : ℝ) ∂(μ : Measure E) < ∞) :
    wasserstein 2 μ ⟨stdGaussian E, inferInstance⟩ ≤
      (2 * klDiv (μ : Measure E) (stdGaussian E)) ^ (1 / 2 : ℝ) := by
  have h := ENNReal.rpow_le_rpow (talagrand_stdGaussian μ hμ) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rwa [← ENNReal.rpow_mul, mul_one_div_cancel two_ne_zero, ENNReal.rpow_one] at h

-- The `T₁` form: since `W₁ ≤ W₂`, the inequality also bounds `W₁(μ, γ)²` by `2 KL(μ ‖ γ)`.
example (μ : ProbabilityMeasure E) (hμ : ∫⁻ x, ‖x‖ₑ ^ (2 : ℝ) ∂(μ : Measure E) < ∞) :
    wasserstein 1 μ ⟨stdGaussian E, inferInstance⟩ ^ (2 : ℝ) ≤
      2 * klDiv (μ : Measure E) (stdGaussian E) :=
  (ENNReal.rpow_le_rpow (wasserstein_mono one_pos one_le_two _ _) (by norm_num)).trans
    (talagrand_stdGaussian μ hμ)

-- Edge case `μ = γ`: the relative entropy vanishes, and so does `W₂(γ, γ)`.
example : wasserstein 2 (⟨stdGaussian E, inferInstance⟩ : ProbabilityMeasure E)
    ⟨stdGaussian E, inferInstance⟩ = 0 := by
  have hγ : ∫⁻ x, ‖x‖ₑ ^ (2 : ℝ) ∂(stdGaussian E) < ∞ := by
    have h := lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top (p := 2) two_ne_zero
      ENNReal.ofNat_ne_top (IsGaussian.memLp_two_id (μ := stdGaussian E)).eLpNorm_lt_top
    simpa using h
  have h := talagrand_stdGaussian ⟨stdGaussian E, inferInstance⟩ hγ
  rw [ProbabilityMeasure.coe_mk, klDiv_self, mul_zero, nonpos_iff_eq_zero,
    ENNReal.rpow_eq_zero_iff] at h
  rcases h with h | h
  · exact h.1
  · norm_num at h

end General

section Real

/-- On `ℝ`, the standard Gaussian measure is `N(0, 1)`: both have characteristic function
`exp (-t² / 2)`. -/
private lemma stdGaussian_real : stdGaussian ℝ = gaussianReal 0 1 := by
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_stdGaussian, charFun_gaussianReal, Real.norm_eq_abs]
  have h : ((|t| : ℝ) : ℂ) ^ 2 = (t : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, sq_abs, Complex.ofReal_pow]
  rw [h]
  push_cast
  ring_nf

-- A sharp instance: `KL(N(m, 1) ‖ N(0, 1)) = m² / 2`, so `W₂(N(m, 1), N(0, 1))² ≤ m²`. The
-- translation `x ↦ x + m` transports `N(0, 1)` onto `N(m, 1)` at cost exactly `m²`.
example (m : ℝ) :
    wasserstein 2 ⟨gaussianReal m 1, inferInstance⟩ ⟨stdGaussian ℝ, inferInstance⟩ ^ (2 : ℝ) ≤
      ENNReal.ofReal (m ^ 2) := by
  have hμ : ∫⁻ x, ‖x‖ₑ ^ (2 : ℝ) ∂(gaussianReal m 1) < ∞ := by
    have h := lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top (p := 2) two_ne_zero
      ENNReal.ofNat_ne_top (memLp_id_gaussianReal' (μ := m) (v := 1) 2 ENNReal.ofNat_ne_top
        |>.eLpNorm_lt_top)
    simpa using h
  have hKL : klDiv (gaussianReal m 1) (stdGaussian ℝ) = ENNReal.ofReal (m ^ 2 / 2) := by
    rw [stdGaussian_real,
      MathlibExt.InformationTheory.ScalarGaussianKL.klDiv_gaussianReal_same_variance m 0 1 one_pos]
    norm_num
  have h := talagrand_stdGaussian (E := ℝ) ⟨gaussianReal m 1, inferInstance⟩ hμ
  rw [ProbabilityMeasure.coe_mk, hKL] at h
  refine h.trans_eq ?_
  rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
  ring_nf

end Real

end MathlibExtTest.TalagrandTransport
