/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Convex.StochasticGradientDescent

open MeasureTheory ProbabilityTheory Real
open scoped RealInnerProductSpace

namespace MathlibExt.Analysis.Convex.StochasticGradientDescent

-- With `t = 1` the average iterate is the deterministic `θ₀`, and the bound reads
-- `f θ₀ - f θ⋆ ≤ D B`, the Lipschitz bound.
example {Ω Ξ E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {μ : Measure Ω}
    [IsProbabilityMeasure μ] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) {θstar : E}
    {ν : Measure Ξ} [IsProbabilityMeasure ν] {G : E → Ξ → E}
    (hGmeas : Measurable (Function.uncurry G)) {B D : ℝ} (hB : 0 < B) (hD : 0 < D)
    (hGbound : ∀ θ ξ, ‖G θ ξ‖ ≤ B) (hGmean : ∀ θ y, f θ + ⟪∫ ξ, G θ ξ ∂ν, y - θ⟫ ≤ f y)
    {ξ : ℕ → Ω → Ξ} (hξmeas : ∀ t, Measurable (ξ t)) (hξindep : iIndepFun ξ μ)
    (hξlaw : ∀ t, μ.map (ξ t) = ν) {θ₀ : E} (hdist : ‖θ₀ - θstar‖ ≤ D) {θ : ℕ → Ω → E}
    (hθ0 : ∀ ω, θ 0 ω = θ₀)
    (hθ : ∀ t ω, θ (t + 1) ω = θ t ω - (D / (B * √((t : ℝ) + 1))) • G (θ t ω) (ξ t ω)) :
    f θ₀ - f θstar ≤ D * B := by
  have h := integral_sgd_average_sub_le hf hGmeas hB hD hGbound hGmean hξmeas hξindep hξlaw
    hdist hθ0 hθ (t := 1) one_pos
  have hpos : (0 : ℝ) < D / (B * √((0 : ℕ) + 1)) := by positivity
  simp only [Finset.range_one, Finset.sum_singleton, hθ0, smul_smul,
    inv_mul_cancel₀ hpos.ne', one_smul, integral_const, probReal_univ, one_smul,
    Nat.cast_one, log_one, sqrt_one] at h
  linarith

end MathlibExt.Analysis.Convex.StochasticGradientDescent
