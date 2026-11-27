/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Analysis.SpecialFunctions.ParabolicCylinder.Basic
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Entire dependence on parabolic-cylinder order

For every fixed complex z, the normalized parabolic-cylinder function U(a,z)
is entire in the complex order a. The defining confluent series at denominator
parameters 1/2 and 3/2 are locally uniformly summable in a, and the reciprocal
Gamma factors are entire, including their zeros at Gamma poles.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Complex

private def coefficient (a : ℂ) (b : ℝ) (n : ℕ) : ℂ :=
  regularizedHGFunCoeff ({a} : Multiset ℂ) ({(b : ℂ)} : Multiset ℂ) n

private lemma coefficient_succ (a : ℂ) (b : ℝ) (hb : 1 / 2 ≤ b) (n : ℕ) :
    coefficient a b (n + 1) = coefficient a b n *
      ((a + n) / (((b : ℂ) + n) * (n + 1))) := by
  have hc : ∀ k ∈ ({(b : ℂ)} : Multiset ℂ), k ≠ -(n : ℂ) := by
    intro k hk
    simp only [Multiset.mem_singleton] at hk
    subst k
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at hr
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have h := regularizedHGFunCoeff_add_one
    (a := ({a} : Multiset ℂ)) (b := ({(b : ℂ)} : Multiset ℂ)) (n := n) hc
  simpa only [coefficient, Multiset.map_singleton, Multiset.prod_singleton] using h

private lemma norm_coefficient_succ (a : ℂ) (b : ℝ) (hb : 1 / 2 ≤ b) (n : ℕ) :
    ‖coefficient a b (n + 1)‖ = ‖coefficient a b n‖ *
      (‖a + n‖ / ((b + n) * (n + 1 : ℝ))) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hbpos : 0 ≤ b + n := by linarith
  have hbnorm : ‖(b : ℂ) + n‖ = b + n := by
    simpa only [Complex.ofReal_add, Complex.ofReal_natCast] using Complex.norm_of_nonneg hbpos
  have hnnorm : ‖(n + 1 : ℂ)‖ = (n + 1 : ℝ) := by
    simpa only [Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one] using
      Complex.norm_of_nonneg (show (0 : ℝ) ≤ n + 1 by positivity)
  rw [coefficient_succ a b hb, norm_mul, norm_div, norm_mul, hbnorm, hnnorm]

private lemma ratio_le (b M : ℝ) (hb : 1 / 2 ≤ b) (hM : 0 ≤ M) (n : ℕ) :
    (M + n) / (b + n) ≤ 2 * M + 1 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hp : 0 < b + n := by linarith
  rw [div_le_iff₀ hp]
  nlinarith [mul_nonneg hM (show 0 ≤ b - 1 / 2 by linarith), mul_nonneg hM hn]

private lemma norm_coefficient_succ_le (a : ℂ) (b M : ℝ)
    (hb : 1 / 2 ≤ b) (hM : 0 ≤ M) (ha : ‖a‖ ≤ M) (n : ℕ) :
    ‖coefficient a b (n + 1)‖ ≤ ‖coefficient a b n‖ * ((2 * M + 1) / (n + 1)) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hp : 0 < b + n := by linarith
  have hnp : (0 : ℝ) < n + 1 := by positivity
  have hna : ‖(n : ℂ)‖ = (n : ℝ) := by simp
  have hnum : ‖a + n‖ ≤ M + n := (norm_add_le a (n : ℂ)).trans (add_le_add ha hna.le)
  rw [norm_coefficient_succ a b hb]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    _ ≤ (M + n) / ((b + n) * (n + 1)) :=
      div_le_div_of_nonneg_right hnum (mul_pos hp hnp).le
    _ = ((M + n) / (b + n)) / (n + 1) := by rw [div_div]
    _ ≤ _ := div_le_div_of_nonneg_right (ratio_le b M hb hM n) hnp.le

private lemma norm_coefficient_le (a : ℂ) (b M : ℝ)
    (hb : 1 / 2 ≤ b) (hM : 0 ≤ M) (ha : ‖a‖ ≤ M) (n : ℕ) :
    ‖coefficient a b n‖ ≤ ‖(Gamma (b : ℂ))⁻¹‖ * (2 * M + 1) ^ n / n.factorial := by
  have hK : 0 ≤ 2 * M + 1 := by positivity
  induction n with
  | zero => simp [coefficient, regularizedHGFunCoeff]
  | succ n ih =>
    calc
      _ ≤ ‖coefficient a b n‖ * ((2 * M + 1) / (n + 1)) :=
        norm_coefficient_succ_le a b M hb hM ha n
      _ ≤ (‖(Gamma (b : ℂ))⁻¹‖ * (2 * M + 1) ^ n / n.factorial) *
          ((2 * M + 1) / (n + 1)) := mul_le_mul_of_nonneg_right ih (by positivity)
      _ = _ := by
        rw [Nat.factorial_succ, pow_succ]
        push_cast
        field_simp

private lemma coefficient_differentiable (b : ℝ) (n : ℕ) (a : ℂ) :
    DifferentiableAt ℂ (fun x : ℂ => coefficient x b n) a := by
  have hfun : (fun x : ℂ => coefficient x b n) = fun x : ℂ =>
      (ascPochhammer ℂ n).eval x / ((n.factorial : ℂ) * Gamma ((b : ℂ) + n)) :=
    funext fun x => regularizedHGFunCoeff_singleton_eq x (b : ℂ) n
  rw [hfun]
  exact (ascPochhammer ℂ n).differentiableAt.div_const _

private lemma norm_term_le (a w : ℂ) (b M : ℝ) (hb : 1 / 2 ≤ b)
    (hM : 0 ≤ M) (ha : ‖a‖ ≤ M) (n : ℕ) :
    ‖coefficient a b n * w ^ n‖ ≤
      ‖(Gamma (b : ℂ))⁻¹‖ * ((2 * M + 1) * ‖w‖) ^ n / n.factorial := by
  rw [norm_mul, norm_pow]
  calc
    _ ≤ (‖(Gamma (b : ℂ))⁻¹‖ * (2 * M + 1) ^ n / n.factorial) * ‖w‖ ^ n :=
      mul_le_mul_of_nonneg_right (norm_coefficient_le a b M hb hM ha n) (by positivity)
    _ = _ := by rw [mul_pow]; ring

private lemma differentiableAt_regularized_order (b : ℝ) (hb : 1 / 2 ≤ b) (w a : ℂ) :
    DifferentiableAt ℂ
      (fun x : ℂ => regularizedHGFun ({x} : Multiset ℂ) ({(b : ℂ)} : Multiset ℂ) w) a := by
  let M : ℝ := ‖a‖ + 1
  let f : ℕ → ℂ → ℂ := fun n x => coefficient x b n * w ^ n
  let u : ℕ → ℝ := fun n =>
    ‖(Gamma (b : ℂ))⁻¹‖ * ((2 * M + 1) * ‖w‖) ^ n / n.factorial
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hu : Summable u := by
    simpa only [u, mul_div_assoc] using
      (Real.summable_pow_div_factorial ((2 * M + 1) * ‖w‖)).mul_left ‖(Gamma (b : ℂ))⁻¹‖
  have hfu : ∀ n x, x ∈ Metric.ball a 1 → ‖f n x‖ ≤ u n := by
    intro n x hx
    have hdist : ‖x - a‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hx
    have hxM : ‖x‖ ≤ M := by
      have h := norm_add_le (x - a) a
      rw [sub_add_cancel] at h
      dsimp [M]
      linarith
    exact norm_term_le x w b M hb hM hxM n
  have hsum := HasSumUniformlyOn.of_norm_le_summable hu hfu
  have hlocal := (hasSumUniformlyOn_iff_tendstoUniformlyOn.mp hsum).tendstoLocallyUniformlyOn
  have hd := hlocal.differentiableOn
    (Filter.Eventually.of_forall fun t x _ =>
      DifferentiableWithinAt.fun_sum fun n _ =>
        ((coefficient_differentiable b n x).mul_const (w ^ n)).differentiableWithinAt)
    Metric.isOpen_ball
  have hda := hd.differentiableAt (Metric.ball_mem_nhds a (by norm_num : (0 : ℝ) < 1))
  have hfun : (fun x : ℂ => ∑' n : ℕ, f n x) =
      (fun x : ℂ => regularizedHGFun ({x} : Multiset ℂ) ({(b : ℂ)} : Multiset ℂ) w) := by
    funext x
    exact (hasSum_regularizedHGFun_singleton x (b : ℂ) w).tsum_eq
  rw [hfun] at hda
  exact hda



private lemma differentiable_regularized_order (b : ℝ) (hb : 1 / 2 ≤ b) (w : ℂ) :
    Differentiable ℂ
      (fun a : ℂ => regularizedHGFun ({a} : Multiset ℂ) ({(b : ℂ)} : Multiset ℂ) w) :=
  fun a => differentiableAt_regularized_order b hb w a

private lemma analyticAt_regularized_order (b : ℝ) (hb : 1 / 2 ≤ b) (w a : ℂ) :
    AnalyticAt ℂ
      (fun x : ℂ => regularizedHGFun ({x} : Multiset ℂ) ({(b : ℂ)} : Multiset ℂ) w) a :=
  (differentiable_regularized_order b hb w).analyticAt a

private lemma analyticAt_inverseGamma_affine (a c : ℂ) :
    AnalyticAt ℂ (fun x : ℂ => (Gamma (x / 2 + c))⁻¹) a := by
  have h := differentiable_one_div_Gamma.analyticAt (a / 2 + c)
  exact h.comp (f := fun x : ℂ => x / 2 + c) (x := a) (by fun_prop)

private lemma analyticAt_prefactor (a : ℂ) :
    AnalyticAt ℂ (fun x : ℂ => (2 : ℂ) ^ (-x / 2 - 1 / 4)) a := by
  simp_rw [cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
  fun_prop

namespace Complex

/-- For every complex a,z, the function x ↦ U(x,z) is complex analytic at a.
All complex orders are included, including zeros of the reciprocal Gamma
coefficients in the defining formula. -/
theorem analyticAt_parabolicCylinderU_order (a z : ℂ) :
    AnalyticAt ℂ (fun x : ℂ => parabolicCylinderU x z) a := by
  have hR0 : AnalyticAt ℂ (fun x : ℂ =>
      regularizedHGFun ({x / 2 + 1 / 4} : Multiset ℂ) ({1 / 2} : Multiset ℂ) (z ^ 2 / 2)) a := by
    have h := (analyticAt_regularized_order (1 / 2) (by norm_num) (z ^ 2 / 2) (a / 2 + 1 / 4)).comp
      (f := fun x : ℂ => x / 2 + 1 / 4) (x := a) (by fun_prop)
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
      Function.comp_def] using h
  have hR1 : AnalyticAt ℂ (fun x : ℂ =>
      regularizedHGFun ({x / 2 + 3 / 4} : Multiset ℂ) ({3 / 2} : Multiset ℂ) (z ^ 2 / 2)) a := by
    have h := (analyticAt_regularized_order (3 / 2) (by norm_num) (z ^ 2 / 2) (a / 2 + 3 / 4)).comp
      (f := fun x : ℂ => x / 2 + 3 / 4) (x := a) (by fun_prop)
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
      Function.comp_def] using h
  have hEven : AnalyticAt ℂ (fun x : ℂ =>
      (Real.sqrt Real.pi : ℂ) * (Gamma (x / 2 + 3 / 4))⁻¹ * Gamma (1 / 2) *
        regularizedHGFun ({x / 2 + 1 / 4} : Multiset ℂ) ({1 / 2} : Multiset ℂ) (z ^ 2 / 2)) a :=
    ((analyticAt_const.mul (analyticAt_inverseGamma_affine a (3 / 4))).mul analyticAt_const).mul hR0
  have hOdd : AnalyticAt ℂ (fun x : ℂ =>
      (Real.sqrt (2 * Real.pi) : ℂ) * (Gamma (x / 2 + 1 / 4))⁻¹ * z * Gamma (3 / 2) *
        regularizedHGFun ({x / 2 + 3 / 4} : Multiset ℂ) ({3 / 2} : Multiset ℂ) (z ^ 2 / 2)) a :=
    (((analyticAt_const.mul (analyticAt_inverseGamma_affine a (1 / 4))).mul analyticAt_const).mul
      analyticAt_const).mul hR1
  have h : AnalyticAt ℂ (fun x : ℂ =>
      (2 : ℂ) ^ (-x / 2 - 1 / 4) * exp (-(z ^ 2) / 4) *
        ((Real.sqrt Real.pi : ℂ) * (Gamma (x / 2 + 3 / 4))⁻¹ * Gamma (1 / 2) *
            regularizedHGFun ({x / 2 + 1 / 4} : Multiset ℂ) ({1 / 2} : Multiset ℂ) (z ^ 2 / 2) -
          (Real.sqrt (2 * Real.pi) : ℂ) * (Gamma (x / 2 + 1 / 4))⁻¹ * z * Gamma (3 / 2) *
            regularizedHGFun ({x / 2 + 3 / 4} : Multiset ℂ) ({3 / 2} : Multiset ℂ) (z ^ 2 / 2))) a :=
    ((analyticAt_prefactor a).mul
    (show AnalyticAt ℂ (fun _ : ℂ => exp (-(z ^ 2) / 4)) a from analyticAt_const)).mul
      (hEven.sub hOdd)
  simpa only [parabolicCylinderU, div_eq_mul_inv] using h

/-- For every complex z, the function a ↦ U(a,z) is complex differentiable
throughout ℂ. -/
@[fun_prop]
theorem differentiable_parabolicCylinderU_order (z : ℂ) :
    Differentiable ℂ (fun a : ℂ => parabolicCylinderU a z) :=
  fun a => (analyticAt_parabolicCylinderU_order a z).differentiableAt

end Complex
