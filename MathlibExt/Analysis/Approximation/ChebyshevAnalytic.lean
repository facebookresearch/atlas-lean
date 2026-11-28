/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import MathlibExt.Analysis.Approximation.ChebyshevSeries

import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Chebyshev coefficients of analytic functions

If `f` is analytic in the open Bernstein ellipse `E_ρ`, `ρ > 1`, with `|f| ≤ M` there, then its
Chebyshev coefficients satisfy `|a_0| ≤ M` and `|a_k| ≤ 2 M ρ^{-k}` for `k ≥ 1`
(`norm_chebCoeff_le_of_analytic`, Theorem 8.1 of L. N. Trefethen, *Approximation Theory and
Approximation Practice*).

The bound on `a_0` holds because `|f| ≤ M` on `[-1, 1]`. For `k ≥ 1` the proof follows
Trefethen's. The Joukowski map `w ↦ (w + w⁻¹) / 2` sends `e^{iθ}` to `cos θ` and the circle
`|w| = s` to the ellipse `|z - 1| + |z + 1| = s + s⁻¹`, so it maps the annulus `1 ≤ |w| < ρ`
into `E_ρ`. This writes `a_k` as `(π i)⁻¹` times the integral of `f((w + w⁻¹) / 2) w^{-k-1}`
over the unit circle. Cauchy's theorem for an annulus moves the contour to the circle `|w| = s`,
`1 < s < ρ`, where the integral is at most `2 π M s^{-k}`, and letting `s → ρ` gives the bound.
-/

open Filter Metric Set Topology
open scoped Real

namespace MathlibExt.Analysis.Approximation.ChebyshevInterpolationWanted

/-- The Joukowski image of `w ≠ 0` has focal distance sum `|w| + |w|⁻¹`. -/
private theorem joukowski_norm_sum {w : ℂ} (hw : w ≠ 0) :
    ‖(w + w⁻¹) / 2 - 1‖ + ‖(w + w⁻¹) / 2 + 1‖ = ‖w‖ + ‖w‖⁻¹ := by
  have h₁ : (w + w⁻¹) / 2 - 1 = (w - 1) ^ 2 / (2 * w) := by field_simp; ring
  have h₂ : (w + w⁻¹) / 2 + 1 = (w + 1) ^ 2 / (2 * w) := by field_simp; ring
  have hpar : ‖w - 1‖ ^ 2 + ‖w + 1‖ ^ 2 = 2 * (‖w‖ ^ 2 + 1) := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.add_re,
      Complex.sub_im, Complex.add_im, Complex.one_re, Complex.one_im]
    ring
  have hw' : 0 < ‖w‖ := norm_pos_iff.mpr hw
  rw [h₁, h₂, norm_div, norm_div, norm_pow, norm_pow, norm_mul, Complex.norm_two]
  field_simp
  linear_combination hpar

/-- The Joukowski map sends `1 ≤ |w| < ρ` into the Bernstein ellipse `E_ρ`. -/
private theorem joukowski_mem {ρ : ℝ} {w : ℂ} (h₁ : 1 ≤ ‖w‖) (h₂ : ‖w‖ < ρ) :
    (w + w⁻¹) / 2 ∈ bernsteinEllipse ρ := by
  have hw : w ≠ 0 := norm_pos_iff.mp (by linarith)
  change ‖(w + w⁻¹) / 2 - 1‖ + ‖(w + w⁻¹) / 2 + 1‖ < ρ + ρ⁻¹
  rw [joukowski_norm_sum hw]
  have ht : 0 < ‖w‖ := by linarith
  have hρ : 0 < ρ := by linarith
  have hkey : ρ + ρ⁻¹ - (‖w‖ + ‖w‖⁻¹) = (ρ - ‖w‖) * (ρ * ‖w‖ - 1) / (ρ * ‖w‖) := by
    field_simp
    ring
  have hpos : 0 < (ρ - ‖w‖) * (ρ * ‖w‖ - 1) / (ρ * ‖w‖) := by
    apply div_pos (mul_pos (by linarith) (by nlinarith)) (mul_pos hρ ht)
  linarith

/-- On the unit circle the Joukowski map is `e^{iθ} ↦ cos θ`. -/
private theorem joukowski_exp (θ : ℝ) :
    (Complex.exp (θ * Complex.I) + (Complex.exp (θ * Complex.I))⁻¹) / 2 =
      ((Real.cos θ : ℝ) : ℂ) := by
  rw [← Complex.exp_neg, Complex.ofReal_cos, Complex.cos]
  ring_nf

private theorem isOpen_bernsteinEllipse (ρ : ℝ) : IsOpen (bernsteinEllipse ρ) :=
  isOpen_lt (by fun_prop) continuous_const

private theorem ofReal_cos_mem {ρ : ℝ} (hρ : 1 < ρ) (θ : ℝ) :
    ((Real.cos θ : ℝ) : ℂ) ∈ bernsteinEllipse ρ := by
  rw [← joukowski_exp]
  exact joukowski_mem (by simp) (by simpa using hρ)

/-- The integrand `f((w + w⁻¹) / 2) w^{-k-1}` is complex differentiable where `1 ≤ |w| < ρ`. -/
private theorem differentiableAt_integrand {ρ : ℝ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (bernsteinEllipse ρ)) (k : ℕ) {w : ℂ} (h₁ : 1 ≤ ‖w‖)
    (h₂ : ‖w‖ < ρ) :
    DifferentiableAt ℂ (fun w => f ((w + w⁻¹) / 2) * (w ^ (k + 1))⁻¹) w := by
  have hw : w ≠ 0 := norm_pos_iff.mp (by linarith)
  have hJ : DifferentiableAt ℂ (fun w : ℂ => (w + w⁻¹) / 2) w :=
    (differentiableAt_id.add (differentiableAt_inv hw)).div_const 2
  have hfJ : DifferentiableAt ℂ f ((w + w⁻¹) / 2) :=
    hf.differentiableAt ((isOpen_bernsteinEllipse ρ).mem_nhds (joukowski_mem h₁ h₂))
  exact (hfJ.comp w hJ).mul ((differentiableAt_pow (k + 1)).inv (pow_ne_zero _ hw))

/-- Over the unit circle, the integral of `f((w + w⁻¹) / 2) w^{-k-1}` is
`2 i ∫_0^π f(cos θ) cos(k θ) dθ`. -/
private theorem circleIntegral_integrand {f : ℂ → ℂ}
    (hfc : Continuous (fun θ : ℝ => f (Real.cos θ))) (k : ℕ) :
    (∮ w in C(0, 1), f ((w + w⁻¹) / 2) * (w ^ (k + 1))⁻¹) =
      2 * Complex.I * ∫ θ in (0 : ℝ)..π, f (Real.cos θ) * (Real.cos (k * θ) : ℂ) := by
  let H : ℝ → ℂ := fun θ =>
    Complex.I * (f (Real.cos θ) * Complex.exp (-(k * (θ * Complex.I))))
  have hH : Continuous H := continuous_const.mul (hfc.mul (by fun_prop))
  have hpt (θ : ℝ) : deriv (circleMap 0 1) θ •
      (f ((circleMap 0 1 θ + (circleMap 0 1 θ)⁻¹) / 2) * (circleMap 0 1 θ ^ (k + 1))⁻¹) =
        H θ := by
    rw [deriv_circleMap, circleMap_zero, Complex.ofReal_one, one_mul, joukowski_exp,
      smul_eq_mul]
    have he : Complex.exp (θ * Complex.I) ≠ 0 := Complex.exp_ne_zero _
    simp only [H, pow_succ, ← Complex.exp_nat_mul, Complex.exp_neg]
    field_simp
  have hrefl (θ : ℝ) : H θ + H (2 * π - θ) =
      2 * Complex.I * (f (Real.cos θ) * (Real.cos (k * θ) : ℂ)) := by
    have hexp : Complex.exp (-(k * (((2 * π - θ : ℝ) : ℂ) * Complex.I))) =
        Complex.exp (k * θ * Complex.I) := by
      rw [show -(k * (((2 * π - θ : ℝ) : ℂ) * Complex.I)) =
          k * θ * Complex.I + -(k * (2 * π * Complex.I)) by push_cast; ring,
        Complex.exp_add, Complex.exp_neg, Complex.exp_nat_mul_two_pi_mul_I, inv_one, mul_one]
    have hcos : ((Real.cos (k * θ) : ℝ) : ℂ) =
        (Complex.exp (k * θ * Complex.I) + Complex.exp (-(k * (θ * Complex.I)))) / 2 := by
      rw [Complex.ofReal_cos, Complex.cos]
      push_cast
      ring_nf
    simp only [H, Real.cos_two_pi_sub, hexp, hcos]
    ring
  calc (∮ w in C(0, 1), f ((w + w⁻¹) / 2) * (w ^ (k + 1))⁻¹)
    _ = ∫ θ in (0 : ℝ)..2 * π, H θ := by
      rw [circleIntegral]
      exact intervalIntegral.integral_congr fun θ _ => hpt θ
    _ = (∫ θ in (0 : ℝ)..π, H θ) + ∫ θ in π..2 * π, H θ :=
      (intervalIntegral.integral_add_adjacent_intervals (hH.intervalIntegrable _ _)
        (hH.intervalIntegrable _ _)).symm
    _ = (∫ θ in (0 : ℝ)..π, H θ) + ∫ θ in (0 : ℝ)..π, H (2 * π - θ) := by
      rw [intervalIntegral.integral_comp_sub_left H (2 * π)]
      congr 2 <;> ring
    _ = ∫ θ in (0 : ℝ)..π, (H θ + H (2 * π - θ)) :=
      (intervalIntegral.integral_add (hH.intervalIntegrable _ _)
        ((hH.comp (by fun_prop)).intervalIntegrable _ _)).symm
    _ = ∫ θ in (0 : ℝ)..π, 2 * Complex.I * (f (Real.cos θ) * (Real.cos (k * θ) : ℂ)) :=
      intervalIntegral.integral_congr fun θ _ => hrefl θ
    _ = _ := intervalIntegral.integral_const_mul _ _

/-- **Chebyshev coefficients of analytic functions** (ATAP Theorem 8.1): if `f` is analytic in the
open Bernstein ellipse `E_ρ`, `ρ > 1`, with `|f| ≤ M` there, then `|a_0| ≤ M` and
`|a_k| ≤ 2 M ρ^{-k}` for `k ≥ 1`. -/
public theorem norm_chebCoeff_le_of_analytic {ρ M : ℝ} (hρ : 1 < ρ) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (bernsteinEllipse ρ))
    (hM : ∀ z ∈ bernsteinEllipse ρ, ‖f z‖ ≤ M) :
    ‖chebCoeff (fun x => f x) 0‖ ≤ M ∧
      ∀ k : ℕ, 1 ≤ k → ‖chebCoeff (fun x => f x) k‖ ≤ 2 * M * (ρ ^ k)⁻¹ := by
  have hfc : Continuous (fun θ : ℝ => f (Real.cos θ)) :=
    hf.continuousOn.comp_continuous (by fun_prop) (ofReal_cos_mem hρ)
  have hπ : 0 < π := Real.pi_pos
  constructor
  · have hint : ‖∫ θ in (0 : ℝ)..π, f (Real.cos θ) * (Real.cos ((0 : ℕ) * θ) : ℂ)‖ ≤
        M * |π - 0| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun θ _ => ?_
      simpa using hM _ (ofReal_cos_mem hρ θ)
    rw [sub_zero, abs_of_pos hπ] at hint
    rw [chebCoeff, ite_eq_left rfl, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    calc 1 / π * ‖∫ θ in (0 : ℝ)..π, f (Real.cos θ) * (Real.cos ((0 : ℕ) * θ) : ℂ)‖
      _ ≤ 1 / π * (M * π) := by gcongr
      _ = M := by field_simp
  · intro k hk
    have hk0 : k ≠ 0 := by omega
    have hρ0 : 0 < ρ := by linarith
    have hcoef : ‖chebCoeff (fun x => f x) k‖ =
        ‖∮ w in C(0, 1), f ((w + w⁻¹) / 2) * (w ^ (k + 1))⁻¹‖ / π := by
      rw [circleIntegral_integrand hfc k, chebCoeff, ite_eq_right hk0, norm_mul, norm_mul,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
        Complex.norm_I, Complex.norm_two]
      field_simp
    have hbound : ∀ s, 1 < s → s < ρ → ‖chebCoeff (fun x => f x) k‖ ≤ 2 * M * (s ^ k)⁻¹ := by
      intro s hs₁ hsρ
      have hd : ∀ w : ℂ, 1 ≤ ‖w‖ → ‖w‖ ≤ s →
          DifferentiableAt ℂ (fun w => f ((w + w⁻¹) / 2) * (w ^ (k + 1))⁻¹) w :=
        fun w h₁ h₂ => differentiableAt_integrand hf k h₁ (h₂.trans_lt hsρ)
      have hann : (∮ w in C(0, s), f ((w + w⁻¹) / 2) * (w ^ (k + 1))⁻¹) =
          ∮ w in C(0, 1), f ((w + w⁻¹) / 2) * (w ^ (k + 1))⁻¹ := by
        refine Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable one_pos
          hs₁.le countable_empty (fun w hw => ?_) (fun w hw => ?_)
        · simp only [Set.mem_sdiff, mem_closedBall, mem_ball, dist_zero_right, not_lt] at hw
          exact (hd w hw.2 hw.1).continuousAt.continuousWithinAt
        · simp only [Set.mem_sdiff, mem_ball, mem_closedBall, dist_zero_right, not_le,
            mem_empty_iff_false, not_false_eq_true, and_true] at hw
          exact hd w hw.2.le hw.1.le
      have hsphere : ∀ w ∈ sphere (0 : ℂ) s,
          ‖f ((w + w⁻¹) / 2) * (w ^ (k + 1))⁻¹‖ ≤ M * (s ^ (k + 1))⁻¹ := by
        intro w hw
        rw [mem_sphere_zero_iff_norm] at hw
        rw [norm_mul, norm_inv, norm_pow, hw]
        gcongr
        exact hM _ (joukowski_mem (by linarith) (by linarith))
      have hle := circleIntegral.norm_integral_le_of_norm_le_const (by linarith) hsphere
      rw [hcoef, ← hann]
      calc ‖∮ w in C(0, s), f ((w + w⁻¹) / 2) * (w ^ (k + 1))⁻¹‖ / π
        _ ≤ 2 * π * s * (M * (s ^ (k + 1))⁻¹) / π := by gcongr
        _ = 2 * M * (s ^ k)⁻¹ := by
          have hs : s ≠ 0 := by linarith
          field_simp
          ring
    have hlim : Tendsto (fun s : ℝ => 2 * M * (s ^ k)⁻¹) (𝓝[<] ρ)
        (𝓝 (2 * M * (ρ ^ k)⁻¹)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds
      exact (((continuous_pow k).continuousAt).inv₀ (pow_ne_zero _ hρ0.ne')).const_mul _
    refine ge_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsLT hρ] with s hs
    exact hbound s hs.1 hs.2

end MathlibExt.Analysis.Approximation.ChebyshevInterpolationWanted
