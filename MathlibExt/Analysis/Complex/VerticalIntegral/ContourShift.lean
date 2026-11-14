/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.LinearCombination

/-!
# Shifting a vertical line integral

Mathlib has Cauchy's theorem for rectangles,
`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`, but no statement that moves a line
integral from one vertical line to another. This file supplies it: if `G` is holomorphic on the
closed strip between `re s = c` and `re s = σ`, absolutely integrable on both lines, and the
horizontal sides of tall rectangles tend to zero, then the two line integrals agree.

## Main statements

* `Complex.tendsto_horizontal_sides_of_norm_le_div_abs_im`: the horizontal sides vanish when
  `‖f s‖ ≤ M / |im s|` on the strip.
* `Complex.integral_vertical_eq_of_tendsto_horizontal`: the contour shift.
-/

@[expose] public section

open Filter MeasureTheory

namespace Complex

/-- **The horizontal sides vanish.** If `‖f s‖ ≤ M / |im s|` on the strip `a ≤ re s ≤ b` for
`|im s| ≥ 1`, then the difference of the horizontal side integrals at heights `∓T` tends to `0`
as `T → ∞`. -/
theorem tendsto_horizontal_sides_of_norm_le_div_abs_im {f : ℂ → ℂ} {a b M : ℝ} (hab : a ≤ b)
    (hf : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 1 ≤ |s.im| → ‖f s‖ ≤ M / |s.im|) :
    Tendsto (fun T : ℝ => (∫ σ in a..b, f (σ + (-T : ℝ) * I)) - ∫ σ in a..b, f (σ + T * I))
      atTop (nhds 0) := by
  have hb : ∀ T : ℝ, 1 ≤ T → ∀ τ : ℝ, |τ| = T →
      ‖∫ σ in a..b, f (σ + τ * I)‖ ≤ M / T * |b - a| := by
    intro T hT τ hτ
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun σ hσ => ?_
    rw [Set.uIoc_of_le hab] at hσ
    have := hf ((σ : ℂ) + τ * I) (by simp; linarith [hσ.1]) (by simp; linarith [hσ.2])
      (by simp; linarith)
    simpa [hτ] using this
  refine squeeze_zero_norm' (a := fun T => 2 * (M / T * |b - a|)) ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with T hT
    have h1 := hb T hT (-T) (by rw [abs_neg, abs_of_pos (by linarith)])
    have h2 := hb T hT T (abs_of_pos (by linarith))
    calc _ ≤ _ := norm_sub_le _ _
      _ ≤ _ := add_le_add h1 h2
      _ = _ := by ring
  · have h : Tendsto (fun T : ℝ => M / T) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    simpa using (h.mul_const |b - a|).const_mul 2

/-- **Shifting an absolutely convergent line integral.** If `G` is holomorphic on every
rectangle `[c, σ] × [-R, R]`, integrable on the lines `re s = c` and `re s = σ`, and the
horizontal sides of these rectangles tend to zero, then
`∫ G (c + it) dt = ∫ G (σ + it) dt`. -/
theorem integral_vertical_eq_of_tendsto_horizontal {G : ℂ → ℂ} {c σ : ℝ}
    (hd : ∀ R : ℝ, 0 < R → DifferentiableOn ℂ G (reProdIm (Set.uIcc c σ) (Set.uIcc (-R) R)))
    (hc : Integrable fun t : ℝ => G (c + t * I)) (hσ : Integrable fun t : ℝ => G (σ + t * I))
    (hhor : Tendsto (fun R : ℝ => (∫ u in c..σ, G (u + (-R : ℝ) * I)) -
      ∫ u in c..σ, G (u + R * I)) atTop (nhds 0)) :
    ∫ t : ℝ, G (c + t * I) = ∫ t : ℝ, G (σ + t * I) := by
  set H : ℝ → ℂ := fun R => ((∫ u in c..σ, G (u + (-R : ℝ) * I)) -
      ∫ u in c..σ, G (u + R * I)) + I * (∫ t in (-R)..R, G (σ + t * I)) -
      I * (∫ t in (-R)..R, G (c + t * I)) with hH
  have hrect : ∀ R : ℝ, 0 < R → H R = 0 := by
    intro R hR
    have h := integral_boundary_rect_eq_zero_of_differentiableOn G (⟨c, -R⟩ : ℂ) (⟨σ, R⟩ : ℂ)
      (hd R hR)
    simpa only [smul_eq_mul, hH] using h
  have hconv : ∀ τ : ℝ, Integrable (fun t : ℝ => G (τ + t * I)) →
      Tendsto (fun R : ℝ => ∫ t in (-R)..R, G (τ + t * I)) atTop
        (nhds (∫ t : ℝ, G (τ + t * I))) := fun τ hτ =>
    intervalIntegral_tendsto_integral hτ tendsto_neg_atTop_atBot tendsto_id
  have hlim : Tendsto H atTop (nhds ((0 : ℂ) + I * (∫ t : ℝ, G (σ + t * I)) -
      I * (∫ t : ℝ, G (c + t * I)))) :=
    (hhor.add ((hconv σ hσ).const_mul I)).sub ((hconv c hc).const_mul I)
  have hzero : Tendsto H atTop (nhds 0) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact (hrect R hR).symm
  have huniq := tendsto_nhds_unique hlim hzero
  have h0 : I * ((∫ t : ℝ, G (σ + t * I)) - ∫ t : ℝ, G (c + t * I)) = 0 := by
    linear_combination huniq
  exact (sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left I_ne_zero)).symm

end Complex
