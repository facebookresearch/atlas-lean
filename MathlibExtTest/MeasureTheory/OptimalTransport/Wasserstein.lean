/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.MeasureTheory.OptimalTransport.Wasserstein

@[expose] public section

open MeasureTheory
open scoped ENNReal
open MathlibExt.MeasureTheory.OptimalTransport.Wasserstein

namespace MathlibExtTest.MeasureTheory.OptimalTransport.Wasserstein

/-- The Dirac probability measure at a real number. -/
noncomputable abbrev δ (x : ℝ) : ProbabilityMeasure ℝ := ⟨Measure.dirac x, inferInstance⟩

/-- Example 6.3 of Villani on `ℝ`: `W_2(δ_3, δ_5) = 2`. -/
example : wasserstein 2 (δ 3) (δ 5) = 2 := by
  rw [wasserstein_dirac (by norm_num), edist_dist, Real.dist_eq]
  norm_num

/-- `W_1(δ_0, δ_1) = 1`, so `W_1` is not identically zero. -/
example : wasserstein 1 (δ 0) (δ 1) = 1 := by
  rw [wasserstein_dirac one_pos, edist_dist, Real.dist_eq]
  norm_num

/-- The triangle inequality applies on the standard Borel space `ℝ`. -/
example (μ₁ μ₂ μ₃ : ProbabilityMeasure ℝ) :
    wasserstein 2 μ₁ μ₃ ≤ wasserstein 2 μ₁ μ₂ + wasserstein 2 μ₂ μ₃ :=
  wasserstein_triangle (by norm_num) μ₁ μ₂ μ₃

/-- Distinct Dirac masses are at positive `W_3` distance, as `eq_of_wasserstein_eq_zero`
predicts. -/
example : wasserstein 3 (δ 0) (δ 1) ≠ 0 := by
  intro h
  have := congrArg (fun μ : ProbabilityMeasure ℝ => (μ : Measure ℝ) {0})
    (eq_of_wasserstein_eq_zero (by norm_num) h)
  simp at this

/-- Monotonicity in the exponent, specialised to `W_1 ≤ W_2`. -/
example (μ ν : ProbabilityMeasure ℝ) : wasserstein 1 μ ν ≤ wasserstein 2 μ ν :=
  wasserstein_mono one_pos (by norm_num) μ ν

/-- The Kantorovich–Rubinstein bound with the `1`-Lipschitz function `x ↦ ‖x‖₊`. -/
example (μ ν : ProbabilityMeasure ℝ) :
    ∫⁻ x, (‖x‖₊ : ℝ≥0∞) ∂(μ : Measure ℝ) ≤
      ∫⁻ x, (‖x‖₊ : ℝ≥0∞) ∂(ν : Measure ℝ) + (1 : NNReal) * wasserstein 1 μ ν :=
  lintegral_le_add_mul_wasserstein_one (g := fun x : ℝ => ‖x‖₊) lipschitzWith_one_nnnorm μ ν

/-- Finite moments give a finite distance: `W_2(δ_0, δ_1) < ∞` via `wasserstein_lt_top`. -/
example : wasserstein 2 (δ 0) (δ 1) < ⊤ :=
  wasserstein_lt_top (by norm_num) (0 : ℝ)
    (by simp [lintegral_dirac]) (by simp [lintegral_dirac, edist_dist])

end MathlibExtTest.MeasureTheory.OptimalTransport.Wasserstein
