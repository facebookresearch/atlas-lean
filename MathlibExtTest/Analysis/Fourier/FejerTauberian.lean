/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Fourier.FejerTauberian
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Group.Integral

/-!
# Tests for the Fejér kernel and the Fejér-kernel Tauberian lemma

The hypotheses of `tendsto_one_of_tendsto_integral_mul_fejer` are met by the Heaviside function
`g = 1_{[0, ∞)}`.
-/

@[expose] public section

open MeasureTheory Filter Topology

example : ∫ x : ℝ, Real.sinc x ^ 2 = Real.pi := Real.integral_sinc_sq

example : Integrable fun x : ℝ => Real.sinc x ^ 2 := Real.integrable_sinc_sq

example : ∫ x : ℝ, Real.sin (2 * x) ^ 2 / (2 * x ^ 2) = Real.pi :=
  Real.integral_sin_sq_div_mul_sq two_pos

/-- Boundary probe: at `λ = 0` the kernel is identically `0`, still integrable. -/
example : Integrable fun x : ℝ => Real.sin (0 * x) ^ 2 / (0 * x ^ 2) :=
  Real.integrable_sin_sq_div_mul_sq 0

/-- Boundary probe: for `λ < 0` the kernel is negative and its integral is `-π`, which is why
`0 < λ` is assumed. -/
example : ∫ x : ℝ, Real.sin (-1 * x) ^ 2 / (-1 * x ^ 2) = -Real.pi := by
  have h := Real.integral_sin_sq_div_mul_sq one_pos
  have : (fun x : ℝ => Real.sin (-1 * x) ^ 2 / (-1 * x ^ 2)) =
      fun x => -(Real.sin (1 * x) ^ 2 / (1 * x ^ 2)) := by
    funext x
    rw [neg_one_mul, Real.sin_neg, neg_sq, neg_one_mul, div_neg, one_mul, one_mul]
  rw [this, integral_neg, h]

/-! ### The Tauberian lemma at the Heaviside function -/

/-- The Heaviside function. -/
private noncomputable def heaviside (u : ℝ) : ℝ := if 0 ≤ u then 1 else 0

private lemma heaviside_monotone : Monotone fun u => Real.exp u * heaviside u := by
  intro a b hab
  simp only [heaviside]
  by_cases ha : 0 ≤ a
  · simp only [ha, hab.trans' ha, ite_true, mul_one]
    exact Real.exp_le_exp.mpr hab
  · simp only [ha, ite_false, mul_zero]
    split <;> positivity

private lemma heaviside_fejer (lam : ℝ) (hlam : 0 < lam) :
    Tendsto (fun v => ∫ u : ℝ, heaviside u *
      (Real.sin (lam * (u - v)) ^ 2 / (lam * (u - v) ^ 2))) atTop (𝓝 Real.pi) := by
  set K : ℝ → ℝ := fun y => Real.sin (lam * y) ^ 2 / (lam * y ^ 2) with hK
  have hshift : ∀ v : ℝ, ∫ u : ℝ, heaviside u * K (u - v) = ∫ y : ℝ, heaviside (y + v) * K y :=
    fun v => by
      rw [← integral_add_right_eq_self (fun u => heaviside u * K (u - v)) v]
      simp only [add_sub_cancel_right]
  simp only [hK] at hshift
  simp_rw [hshift]
  rw [← Real.integral_sin_sq_div_mul_sq hlam]
  have hKnn : ∀ y : ℝ, 0 ≤ K y := fun y => by positivity
  refine tendsto_integral_filter_of_dominated_convergence K (Eventually.of_forall fun v => ?_)
    (Eventually.of_forall fun v => Eventually.of_forall fun y => ?_)
    (Real.integrable_sin_sq_div_mul_sq lam) (Eventually.of_forall fun y => ?_)
  · refine (Measurable.mul ?_ (by fun_prop)).aestronglyMeasurable
    exact Measurable.ite (measurableSet_le measurable_const (measurable_id.add_const v))
      measurable_const measurable_const
  · simp only [heaviside]
    split
    · rw [one_mul, Real.norm_of_nonneg (hKnn y)]
    · rw [zero_mul, norm_zero]; exact hKnn y
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (-y)] with v hv
    simp only [heaviside, show 0 ≤ y + v by linarith, ite_true, one_mul]

/-- **The Tauberian lemma is non-vacuous.** At the Heaviside function, `g v → 1`. -/
example : Tendsto heaviside atTop (𝓝 1) :=
  tendsto_one_of_tendsto_integral_mul_fejer (fun u hu => by simp [heaviside, not_le.mpr hu])
    heaviside_monotone heaviside_fejer
