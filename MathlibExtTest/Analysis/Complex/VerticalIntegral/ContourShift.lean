/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.VerticalIntegral.ContourShift
public import MathlibExt.Analysis.Complex.VerticalIntegral.Integrable
public import MathlibExt.Analysis.Complex.VerticalIntegral.CauchyKernel

/-!
# Tests for shifting a vertical line integral

The hypotheses of `Complex.integral_vertical_eq_of_tendsto_horizontal` are met by
`G s = (s + 1)⁻²` between `re s = 1` and `re s = 2`.
-/

@[expose] public section

open Complex MeasureTheory Filter

private lemma abs_im_le_norm_add_one (s : ℂ) : |s.im| ≤ ‖s + 1‖ := by
  simpa using abs_im_le_norm (s + 1)

/-- `‖(s + 1)⁻²‖ ≤ 1 / |im s|` once `|im s| ≥ 1`. -/
private lemma norm_inv_add_one_sq_le {s : ℂ} (hs : 1 ≤ |s.im|) :
    ‖((s + 1) ^ 2)⁻¹‖ ≤ 1 / |s.im| := by
  have h1 := abs_im_le_norm_add_one s
  have hpos : 0 < |s.im| := by linarith
  rw [norm_inv, norm_pow, one_div]
  refine inv_anti₀ hpos ?_
  nlinarith

/-- The horizontal sides vanish. -/
example : Tendsto (fun T : ℝ => (∫ σ in (1 : ℝ)..2, ((((σ : ℂ) + (-T : ℝ) * I) + 1) ^ 2)⁻¹) -
    ∫ σ in (1 : ℝ)..2, ((((σ : ℂ) + T * I) + 1) ^ 2)⁻¹) atTop (nhds 0) :=
  tendsto_horizontal_sides_of_norm_le_div_abs_im (f := fun s => ((s + 1) ^ 2)⁻¹) (M := 1)
    (by norm_num) fun s _ _ hs => norm_inv_add_one_sq_le hs

/-- The test integrand `(s + 1)⁻²`. -/
private noncomputable def G (s : ℂ) : ℂ := ((s + 1) ^ 2)⁻¹

private lemma integrable_line {c : ℝ} (hc : 0 < c) :
    Integrable fun t : ℝ => G ((c : ℂ) + t * I) := by
  have h : ∀ t : ℝ, G ((c : ℂ) + t * I) = (((((c + 1 : ℝ) : ℂ) + t * I)) ^ 2)⁻¹ := fun t => by
    simp only [G]; push_cast; ring_nf
  simp_rw [h]
  refine integrable_of_norm_le_div_pow (c := c + 1) (n := 0) (M := 1) (by linarith) zero_le_one
    ?_ fun t => by simp
  refine Continuous.inv₀ (by fun_prop) fun t => ?_
  exact pow_ne_zero 2 (ofReal_add_mul_I_ne_zero (Or.inl (by linarith)))

/-- **The contour shift.** `∫ G (1 + it) dt = ∫ G (2 + it) dt`. -/
example : ∫ t : ℝ, G ((1 : ℝ) + t * I) = ∫ t : ℝ, G ((2 : ℝ) + t * I) := by
  refine integral_vertical_eq_of_tendsto_horizontal (fun R _ => ?_) (integrable_line one_pos)
    (integrable_line two_pos)
    (tendsto_horizontal_sides_of_norm_le_div_abs_im (M := 1) (by norm_num)
      fun s _ _ hs => norm_inv_add_one_sq_le hs)
  intro s hs
  have hre : 1 ≤ s.re := by
    have := hs.1
    rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at this
    exact this.1
  refine (DifferentiableAt.inv (by fun_prop) ?_).differentiableWithinAt
  refine pow_ne_zero 2 fun h => ?_
  have := congrArg re h
  simp at this
  linarith
