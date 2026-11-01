/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Sufficiency.RaoBlackwell

@[expose] public section

open MeasureTheory MathlibExt.Probability.Statistics.Sufficiency

namespace MathlibExtTest.Probability.Statistics.Sufficiency.RaoBlackwell

/-- Conditioning on the trivial σ-algebra recovers the bias–variance decomposition:
`E (W - c)² = (E W - c)² + E (W - E W)²`. -/
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {W : Ω → ℝ}
    (hW : MemLp W 2 μ) (c : ℝ) :
    ∫ ω, (W ω - c) ^ 2 ∂μ = (∫ ω, W ω ∂μ - c) ^ 2 + ∫ ω, (W ω - ∫ ω', W ω' ∂μ) ^ 2 ∂μ := by
  have h := integral_sq_sub_eq_add bot_le μ hW c
  rw [condExp_bot] at h
  simpa using h

/-- The convex-loss inequality with absolute loss and the trivial σ-algebra:
`|E W - c| ≤ E |W - c|`. -/
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {W : Ω → ℝ}
    (hW : Integrable W μ) (c : ℝ) : |∫ ω, W ω ∂μ - c| ≤ ∫ ω, |W ω - c| ∂μ := by
  have hL : ConvexOn ℝ Set.univ fun x : ℝ => |x - c| := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    have : a • x + b • y - c = a * (x - c) + b * (y - c) := by
      simp only [smul_eq_mul]
      linear_combination c * hab
    simp only [smul_eq_mul] at this ⊢
    rw [this]
    calc |a * (x - c) + b * (y - c)| ≤ |a * (x - c)| + |b * (y - c)| := abs_add_le _ _
      _ = a * |x - c| + b * |y - c| := by rw [abs_mul, abs_mul, abs_of_nonneg ha,
          abs_of_nonneg hb]
  have h := integral_comp_condExp_le bot_le μ hL hW ((hW.sub (integrable_const c)).abs)
  rw [condExp_bot] at h
  simpa using h

/-- Non-vacuity of the family theorem: a one-law family is sufficient for every
sub-σ-algebra, so the Rao–Blackwell estimator is `μ[W | m]` itself. -/
example {Ω : Type*} {m m₀ : MeasurableSpace Ω} (hm : m ≤ m₀) (μ : Measure[m₀] Ω)
    [IsProbabilityMeasure μ] {W : Ω → ℝ} (hWm : Measurable[m₀] W) (hW : Integrable W μ) :
    ∃ η : Ω → ℝ, StronglyMeasurable[m] η ∧ η =ᵐ[μ] μ[W | m] ∧ ∫ ω, η ω ∂μ = ∫ ω, W ω ∂μ := by
  have hP : IsSufficient m (fun _ : Unit => μ) := fun s _ =>
    ⟨μ[s.indicator fun _ => (1 : ℝ) | m], stronglyMeasurable_condExp, fun _ => .rfl⟩
  obtain ⟨η, hη, hver, hmean, -⟩ :=
    IsSufficient.raoBlackwell hm hP hWm (fun _ => hW)
  exact ⟨η, hη, hver (), hmean ()⟩

end MathlibExtTest.Probability.Statistics.Sufficiency.RaoBlackwell
