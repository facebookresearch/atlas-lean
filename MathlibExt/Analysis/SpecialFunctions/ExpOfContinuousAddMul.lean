/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace MetaMathlibExt

@[expose] public section

/-! # Exponentials of continuous additive-to-multiplicative maps -/

open scoped Interval Topology

/-- **Continuous solutions of the exponential functional equation.** If a continuous function
$f : \mathbb{R} \to \mathbb{C}$ satisfies $f(0) = 1$ and $f(r + s) = f(r) f(s)$ for all real $r$
and $s$, then there is a complex number $L$ such that $f(r) = e^{rL}$ for every real $r$. -/
theorem exists_eq_exp_mul_of_continuous_add_mul (f : ℝ → ℂ) (hf : Continuous f)
    (hzero : f 0 = 1) (hadd : ∀ r s : ℝ, f (r + s) = f r * f s) :
    ∃ L : ℂ, ∀ r : ℝ, f r = Complex.exp ((r : ℂ) * L) := by
  have hnear : {x : ℝ | ‖f x - 1‖ < (1 / 2 : ℝ)} ∈ 𝓝 0 := by
    have h := hf.continuousAt.preimage_mem_nhds
      (Metric.ball_mem_nhds (f 0) (by norm_num : (0 : ℝ) < 1 / 2))
    rw [hzero] at h
    filter_upwards [h] with x hx
    change f x ∈ Metric.ball (1 : ℂ) (1 / 2 : ℝ) at hx
    simpa only [Metric.mem_ball, dist_eq_norm] using hx
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let d : ℝ := ε / 2
  have hd : 0 < d := by simp only [d]; positivity
  have hbound : ∀ x ∈ Ι (0 : ℝ) d, ‖f x - 1‖ ≤ (1 / 2 : ℝ) := by
    intro x hx
    have hxIoc : x ∈ Set.Ioc (0 : ℝ) d := by
      simpa only [Set.uIoc_of_le hd.le] using hx
    have hxball : x ∈ Metric.ball (0 : ℝ) ε := by
      rw [Metric.mem_ball, Real.dist_eq]
      simp only [sub_zero, abs_of_nonneg hxIoc.1.le]
      simp only [d] at hxIoc
      linarith [hxIoc.2]
    exact (hball hxball).le
  let c : ℂ := ∫ x in (0 : ℝ)..d, f x
  have hfint : IntervalIntegrable f MeasureTheory.volume 0 d := hf.intervalIntegrable _ _
  have honeint : IntervalIntegrable (fun _ : ℝ => (1 : ℂ)) MeasureTheory.volume 0 d :=
    continuous_const.intervalIntegrable _ _
  have hdiff_eq : (∫ x in (0 : ℝ)..d, f x - 1) = c - (d : ℂ) := by
    simp only [c]
    rw [intervalIntegral.integral_sub hfint honeint]
    simp
  have hdiff : ‖c - (d : ℂ)‖ ≤ (1 / 2 : ℝ) * d := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    rw [hdiff_eq] at h
    simpa only [sub_zero, abs_of_pos hd] using h
  have hc : c ≠ 0 := by
    intro hc
    rw [hc, zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd] at hdiff
    nlinarith
  let A : ℝ → ℂ := fun x => ∫ t in (0 : ℝ)..x, f t
  have hA (x : ℝ) : HasDerivAt A (f x) x := by
    exact intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 x)
      (hf.stronglyMeasurableAtFilter MeasureTheory.volume (𝓝 x)) hf.continuousAt
  have hAdiff (x : ℝ) : A (x + d) - A x = ∫ t in x..x + d, f t := by
    apply sub_eq_iff_eq_add.mpr
    calc
      A (x + d) = A x + ∫ t in x..x + d, f t := by
        exact (intervalIntegral.integral_add_adjacent_intervals
          (hf.intervalIntegrable 0 x) (hf.intervalIntegrable x (x + d))).symm
      _ = (∫ t in x..x + d, f t) + A x := add_comm _ _
  have hshift (x : ℝ) : f x * c = ∫ t in x..x + d, f t := by
    calc
      f x * c = ∫ t in (0 : ℝ)..d, f x * f t := by simp [c]
      _ = ∫ t in (0 : ℝ)..d, f (x + t) := by
        apply intervalIntegral.integral_congr
        intro t _
        change f x * f t = f (x + t)
        rw [hadd]
      _ = ∫ t in x..x + d, f t := by
        simpa only [add_comm, add_zero, zero_add] using
          (intervalIntegral.integral_comp_add_right (f := f) (a := 0) (b := d) x)
  have hmulA (x : ℝ) : f x * c = A (x + d) - A x :=
    (hshift x).trans (hAdiff x).symm
  have hH (x : ℝ) :
      HasDerivAt (fun y : ℝ => A (y + d) - A y) (f (x + d) - f x) x := by
    have hfirst : HasDerivAt (fun y : ℝ => A (y + d)) (f (x + d)) x := by
      simpa [Function.comp_def] using
        (hA (id x + d)).scomp x ((hasDerivAt_id x).add_const d)
    exact hfirst.sub (hA x)
  have hmul (x : ℝ) : HasDerivAt (fun y : ℝ => f y * c) (f (x + d) - f x) x := by
    have heq : (fun y : ℝ => f y * c) = fun y : ℝ => A (y + d) - A y :=
      funext hmulA
    rw [heq]
    exact hH x
  let L : ℂ := (f d - 1) * c⁻¹
  have hfderiv (x : ℝ) : HasDerivAt f (f x * L) x := by
    have hscaled := (hmul x).mul_const c⁻¹
    have hfun : (fun y : ℝ => f y * c * c⁻¹) = f := by
      funext y
      rw [mul_assoc, mul_inv_cancel₀ hc, mul_one]
    rw [hfun] at hscaled
    convert hscaled using 1
    rw [hadd]
    simp only [L]
    ring
  let g : ℝ → ℂ := fun x => f x * Complex.exp ((x : ℂ) * (-L))
  have hexp (x : ℝ) :
      HasDerivAt (fun y : ℝ => Complex.exp ((y : ℂ) * (-L)))
        (Complex.exp ((x : ℂ) * (-L)) * (-L)) x := by
    have hlin : HasDerivAt (fun y : ℝ => (y : ℂ) * (-L)) (-L) x := by
      exact (hasDerivAt_mul_const (-L)).comp_ofReal
    exact hlin.cexp
  have hgderiv (x : ℝ) : HasDerivAt g 0 x := by
    have h := (hfderiv x).mul (hexp x)
    change HasDerivAt (fun y : ℝ => f y * Complex.exp ((y : ℂ) * (-L))) 0 x
    convert h using 1
    ring
  have hgdiff : Differentiable ℝ g := fun x => (hgderiv x).differentiableAt
  have hgzero : ∀ x : ℝ, deriv g x = 0 := fun x => (hgderiv x).deriv
  refine ⟨L, fun x => ?_⟩
  have hxg : g x = g 0 := is_const_of_deriv_eq_zero hgdiff hgzero x 0
  have hxone : f x * Complex.exp ((x : ℂ) * (-L)) = 1 := by
    simpa only [g, hzero, Complex.ofReal_zero, zero_mul, neg_zero, Complex.exp_zero, mul_one]
      using hxg
  rw [mul_neg, Complex.exp_neg] at hxone
  exact (mul_inv_eq_one₀ (Complex.exp_ne_zero ((x : ℂ) * L))).mp hxone

end

end MetaMathlibExt
