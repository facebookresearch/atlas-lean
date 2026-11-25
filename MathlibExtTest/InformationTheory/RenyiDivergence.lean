/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.RenyiDivergence

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MathlibExtTest.InformationTheory.RenyiDivergence

open MathlibExt.InformationTheory.RenyiDivergence

/-- Order `1` is outside the domain: moment `∞`, divergence `⊤`. -/
example (μ ν : Measure ℝ) : renyiMoment μ ν 1 = ∞ ∧ renyiDiv μ ν 1 = ⊤ :=
  ⟨renyiMoment_of_le_one le_rfl, renyiDiv_of_le_one le_rfl⟩

/-- Order `1 / 2` is outside the domain (regression for the order gate). -/
example (μ ν : Measure ℝ) : renyiMoment μ ν (1 / 2) = ∞ ∧ renyiDiv μ ν (1 / 2) = ⊤ :=
  ⟨renyiMoment_of_le_one (by norm_num), renyiDiv_of_le_one (by norm_num)⟩

/-- Point masses at different points are not absolutely continuous: `⊤`. -/
example : renyiDiv (Measure.dirac (0 : ℝ)) (Measure.dirac 1) 2 = ⊤ := by
  apply renyiDiv_of_not_ac
  intro h
  have h1 := h (show Measure.dirac (1 : ℝ) {0} = 0 by simp)
  simp at h1

/-- Equal laws give `0`, through `renyiDiv_self` and through the closed form. -/
example : renyiDiv (gaussianReal 3 2) (gaussianReal 3 2) 2 = 0 :=
  renyiDiv_self _ (by norm_num)

example : renyiDiv (gaussianReal 3 2) (gaussianReal 3 2) 2 = 0 := by
  rw [renyiDiv_gaussianReal 3 3 (by norm_num) (by norm_num)]
  norm_num

/-- Shifted instance: order `2`, means `1` and `4`, variance `3`: moment `exp 3`. -/
example : renyiMoment (gaussianReal 1 3) (gaussianReal 4 3) 2 = ENNReal.ofReal (Real.exp 3) := by
  rw [renyiMoment_gaussianReal 1 4 (by norm_num) (by norm_num)]
  norm_num

/-- Shifted instance: divergence `2 · 3² / (2 · 3) = 3`. -/
example : renyiDiv (gaussianReal 1 3) (gaussianReal 4 3) 2 = ((3 : ℝ) : EReal) := by
  rw [renyiDiv_gaussianReal 1 4 (by norm_num) (by norm_num)]
  norm_num

/-- Source form of Proposition 7: `D_α(N(0, σ²) ‖ N(μ, σ²)) = α μ² / (2 σ²)` for `σ ≠ 0`. -/
example (σ μ α : ℝ) (hσ : σ ≠ 0) (hα : 1 < α) :
    renyiDiv (gaussianReal 0 (σ ^ 2).toNNReal) (gaussianReal μ (σ ^ 2).toNNReal) α =
      ((α * μ ^ 2 / (2 * σ ^ 2) : ℝ) : EReal) := by
  have hv : (σ ^ 2).toNNReal ≠ 0 := by
    rw [Ne, Real.toNNReal_eq_zero, not_le]
    exact lt_of_le_of_ne (sq_nonneg σ) (Ne.symm (pow_ne_zero 2 hσ))
  rw [renyiDiv_gaussianReal 0 μ hv hα, Real.coe_toNNReal _ (sq_nonneg σ)]
  congr 1
  ring

/-- Zero variance, distinct means: point masses, divergence `⊤`. -/
example : renyiDiv (gaussianReal 0 0) (gaussianReal 1 0) 2 = ⊤ := by
  rw [gaussianReal_zero_var, gaussianReal_zero_var]
  apply renyiDiv_of_not_ac
  intro h
  have h1 := h (show Measure.dirac (1 : ℝ) {0} = 0 by simp)
  simp at h1

/-- At variance `0` the closed form is a finite real (`x / 0 = 0`), so `hv` cannot be dropped. -/
example : renyiDiv (gaussianReal 0 0) (gaussianReal 1 0) 2 ≠
    ((2 * (0 - 1) ^ 2 / (2 * ((0 : ℝ≥0) : ℝ)) : ℝ) : EReal) := by
  rw [gaussianReal_zero_var, gaussianReal_zero_var, renyiDiv_of_not_ac]
  · exact (EReal.coe_ne_top _).symm
  · intro h
    have h1 := h (show Measure.dirac (1 : ℝ) {0} = 0 by simp)
    simp at h1

/-- Unequal variances: no closed form here, but nonnegativity applies. -/
example : 0 ≤ renyiDiv (gaussianReal 0 1) (gaussianReal 5 2) 3 := renyiDiv_nonneg _ _ _

/-- Gaussian-mechanism curve: `|1 - 4| ≤ 3` at order `2` and variance `3` gives at most `3`. -/
example :
    renyiDiv (gaussianReal 1 3) (gaussianReal 4 3) 2 ≤ ((2 * 3 ^ 2 / (2 * 3) : ℝ) : EReal) :=
  renyiDiv_gaussianReal_le 1 4 (by norm_num) (by norm_num) (by norm_num [abs_of_neg])

/-- Outside probability measures: the zero measure gives `⊥` (no divergence meaning). -/
example : renyiDiv (0 : Measure ℝ) (gaussianReal 0 1) 2 = ⊥ := by
  rw [renyiDiv_of_one_lt (by norm_num),
    renyiMoment_of_ac (Measure.AbsolutelyContinuous.zero _) (by norm_num),
    lintegral_congr_ae (g := fun _ => (0 : ℝ≥0∞))
      (by filter_upwards [Measure.rnDeriv_zero (gaussianReal 0 1)] with x hx; simp [hx])]
  simp only [lintegral_zero, ENNReal.log_zero]
  exact EReal.coe_mul_bot_of_pos (by norm_num)

end MathlibExtTest.InformationTheory.RenyiDivergence
