/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The Dirichlet form of linear Brownian motion

For smooth compactly supported functions on the real line, the Gaussian semigroup
approximations converge to half the integral of the squared derivative.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped NNReal ContDiff

namespace MathlibExt.Probability.DirichletFormWanted

private lemma taylor_error_le {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    {M : ℝ} (hM : ∀ x, ‖iteratedDeriv 3 f x‖ ≤ M) (x y : ℝ) :
    ‖f (x + y) - (f x + deriv f x * y + iteratedDeriv 2 f x / 2 * y ^ 2)‖ ≤
      M / 6 * ‖y‖ ^ 3 := by
  by_cases hy : y = 0
  · simp [hy]
  have hxy : x ≠ x + y := by simpa using hy
  have hu := uniqueDiffOn_uIcc hxy
  have hs := Set.left_mem_uIcc (a := x) (b := x + y)
  obtain ⟨z, _, hz⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (n := 2) hxy
      (hf.of_le (by simp)).contDiffOn
  have h1 : iteratedDerivWithin 1 f (Set.uIcc x (x + y)) x = deriv f x := by
    simpa only [iteratedDeriv_one] using
      iteratedDerivWithin_eq_iteratedDeriv (n := 1) hu (hf.contDiffAt.of_le (by simp)) hs
  have h2 : iteratedDerivWithin 2 f (Set.uIcc x (x + y)) x = iteratedDeriv 2 f x :=
    iteratedDerivWithin_eq_iteratedDeriv hu (hf.contDiffAt.of_le (by simp)) hs
  have hpoly : taylorWithinEval f 2 (Set.uIcc x (x + y)) x (x + y) =
      f x + deriv f x * y + iteratedDeriv 2 f x / 2 * y ^ 2 := by
    rw [taylor_within_apply, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    norm_num [h1, h2, smul_eq_mul]
    ring
  rw [← hpoly, hz]
  norm_num [Nat.factorial, norm_div, norm_mul, norm_pow]
  calc
    ‖iteratedDeriv 3 f z‖ * ‖y‖ ^ 3 / 6 ≤ M * ‖y‖ ^ 3 / 6 := by
      gcongr
      exact hM z
    _ = M / 6 * ‖y‖ ^ 3 := by ring

-- A centered Gaussian is a scaled standard Gaussian, including at variance zero.
private lemma gaussian_third_norm_moment (t : ℝ≥0) :
    ∫ y : ℝ, ‖y‖ ^ 3 ∂gaussianReal 0 t =
      √(t : ℝ) ^ 3 * ∫ y : ℝ, ‖y‖ ^ 3 ∂gaussianReal 0 1 := by
  have hmap : (gaussianReal 0 1).map (fun y ↦ √(t : ℝ) * y) = gaussianReal 0 t := by
    rw [gaussianReal_map_const_mul, mul_zero, mul_one]
    congr 1
    exact NNReal.eq (Real.sq_sqrt t.coe_nonneg)
  rw [← hmap, integral_map (by fun_prop) (by fun_prop), ← integral_const_mul]
  simp [norm_mul, mul_pow, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]

private lemma gaussian_norm_pow_integrable (t : ℝ≥0) (n : ℕ) :
    Integrable (fun y : ℝ ↦ ‖y‖ ^ n) (gaussianReal 0 t) := by
  simpa only [ENNReal.coe_natCast, id_eq] using
    (memLp_id_gaussianReal (μ := 0) (v := t) (n : ℝ≥0)).integrable_norm_pow' (p := n)

-- Integrate the Taylor polynomial using the mean and variance.
private lemma gaussian_taylor_error_le {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) {M : ℝ} (hM : ∀ x, ‖iteratedDeriv 3 f x‖ ≤ M)
    (x : ℝ) (t : ℝ≥0) :
    ‖(∫ y, f (x + y) ∂gaussianReal 0 t) - (f x + iteratedDeriv 2 f x / 2 * t)‖ ≤
      (M / 6 * ∫ y : ℝ, ‖y‖ ^ 3 ∂gaussianReal 0 1) * √(t : ℝ) ^ 3 := by
  let μ := gaussianReal 0 t
  let p := fun y : ℝ ↦ f x + deriv f x * y + iteratedDeriv 2 f x / 2 * y ^ 2
  obtain ⟨B, hB⟩ := hfc.exists_bound_of_continuous hf.continuous
  have hf_int : Integrable (fun y ↦ f (x + y)) μ :=
    Integrable.of_bound (by fun_prop) B (Filter.Eventually.of_forall fun y ↦ hB (x + y))
  have hlin : Integrable (fun y : ℝ ↦ y) μ :=
    memLp_one_iff_integrable.mp (memLp_id_gaussianReal (μ := 0) (v := t) 1)
  have hquad : Integrable (fun y : ℝ ↦ y ^ 2) μ := by
    simpa only [Real.norm_eq_abs, sq_abs] using gaussian_norm_pow_integrable t 2
  have hsecond : ∫ y : ℝ, y ^ 2 ∂μ = t := by
    have hv := variance_fun_id_gaussianReal (μ := 0) (v := t)
    rw [variance_eq_integral (by fun_prop), integral_id_gaussianReal] at hv
    simpa only [sub_zero] using hv
  have hsum : Integrable (fun y : ℝ ↦ f x + deriv f x * y) μ :=
    (integrable_const _).add (hlin.const_mul _)
  have hp_int : Integrable p μ := hsum.add (hquad.const_mul _)
  have hp : ∫ y, p y ∂μ = f x + iteratedDeriv 2 f x / 2 * t := by
    dsimp only [p]
    rw [integral_add hsum (hquad.const_mul _),
      integral_add (integrable_const _) (hlin.const_mul _),
      integral_const_mul, integral_const_mul, hsecond]
    simp [μ]
  rw [← hp, ← integral_sub hf_int hp_int]
  calc
    ‖∫ y, f (x + y) - p y ∂μ‖ ≤ ∫ y : ℝ, M / 6 * ‖y‖ ^ 3 ∂μ :=
      norm_integral_le_of_norm_le ((gaussian_norm_pow_integrable t 3).const_mul _)
        (Filter.Eventually.of_forall fun y ↦ taylor_error_le hf hM x y)
    _ = _ := by
      rw [integral_const_mul]
      change M / 6 * (∫ y : ℝ, ‖y‖ ^ 3 ∂gaussianReal 0 t) = _
      rw [gaussian_third_norm_moment]
      ring

/-- **The Dirichlet form of linear Brownian motion is `½ ∫ f'²`.** For a smooth compactly
supported `f : ℝ → ℝ`, with `T_t f(x) = E f(x + B_t) = ∫ f(x + y) N(0, t)(dy)` the Brownian
semigroup, the approximating forms `(1/t)(f - T_t f, f)_{L²}` tend to `½ ∫ f'(x)² dx` as
`t ↓ 0`. This is the case `d = 1`, `u ∈ C_c^∞(ℝ)` of Fukushima, Oshima and Takeda, *Dirichlet
Forms and Symmetric Markov Processes*, 2nd ed., 2011, Example 4.2.1 (the Dirichlet form of
`d`-dimensional Brownian motion is `(½ D, H¹(ℝ^d))`, with the Gaussian semigroup (1.4.25)),
combined with their Lemma 1.3.4(i) (`E(u, u) = lim_{t ↓ 0} (1/t)(u - T_t u, u)`). -/
public theorem tendsto_brownian_approximatingForm {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) :
    Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ * ∫ x, f x * (f x - ∫ y, f (x + y) ∂gaussianReal 0 t))
      (𝓝[>] 0) (𝓝 (1 / 2 * ∫ x, deriv f x ^ 2)) := by
  have hf1 : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
  have hf2 : Continuous (iteratedDeriv 2 f) := ContDiff.continuous_iteratedDeriv 2 hf (by simp)
  have hf3 : Continuous (iteratedDeriv 3 f) := ContDiff.continuous_iteratedDeriv 3 hf (by simp)
  have hfc3 : HasCompactSupport (iteratedDeriv 3 f) := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hfc.deriv.deriv.deriv
  have hprod : Integrable (fun x ↦ f x * iteratedDeriv 2 f x) :=
    (hf.continuous.mul hf2).integrable_of_hasCompactSupport hfc.mul_right
  -- Integration by parts identifies the limiting energy.
  have hparts : (∫ x, f x * iteratedDeriv 2 f x) = -(∫ x, deriv f x ^ 2) := by
    have hd (x : ℝ) : HasDerivAt (deriv f) (iteratedDeriv 2 f x) x := by
      simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
        (hf1.differentiable (by simp) x).hasDerivAt
    have hsq : Integrable (fun x ↦ deriv f x * deriv f x) :=
      (hf1.continuous.mul hf1.continuous).integrable_of_hasCompactSupport hfc.deriv.mul_right
    have hcross : Integrable (fun x ↦ f x * deriv f x) :=
      (hf.continuous.mul hf1.continuous).integrable_of_hasCompactSupport hfc.mul_right
    simpa only [pow_two] using integral_mul_deriv_eq_deriv_mul_of_integrable
      (fun x _ ↦ (hf.differentiable (by simp) x).hasDerivAt) (fun x _ ↦ hd x) hprod hsq hcross
  obtain ⟨M, hM⟩ := hfc3.exists_bound_of_continuous hf3
  let C := M / 6 * ∫ y : ℝ, ‖y‖ ^ 3 ∂gaussianReal 0 1
  let avg := fun (t : ℝ≥0) (x : ℝ) ↦ ∫ y, f (x + y) ∂gaussianReal 0 t
  let r := fun (t : ℝ≥0) (x : ℝ) ↦ f x * (avg t x - (f x + iteratedDeriv 2 f x / 2 * t))
  have hbound (t : ℝ≥0) (x : ℝ) : ‖r t x‖ ≤ C * √(t : ℝ) ^ 3 * ‖f x‖ := by
    change ‖f x * (avg t x - (f x + iteratedDeriv 2 f x / 2 * t))‖ ≤ _
    rw [norm_mul, mul_comm ‖f x‖]
    exact mul_le_mul_of_nonneg_right (gaussian_taylor_error_le hf hfc hM x t) (norm_nonneg _)
  have hf_norm : Integrable (fun x ↦ ‖f x‖) :=
    (hf.continuous.integrable_of_hasCompactSupport hfc).norm
  have hr_int (t : ℝ≥0) : Integrable (r t) := by
    have htranslate : Continuous (fun p : ℝ × ℝ ↦ f (p.1 + p.2)) := by fun_prop
    have havg : StronglyMeasurable (avg t) :=
      htranslate.stronglyMeasurable.integral_prod_right' (ν := gaussianReal 0 t)
    refine Integrable.mono' (hf_norm.const_mul (C * √(t : ℝ) ^ 3)) ?_
      (Filter.Eventually.of_forall (hbound t))
    have hp : Continuous (fun x ↦ f x + iteratedDeriv 2 f x / 2 * (t : ℝ)) := by fun_prop
    exact (hf.continuous.stronglyMeasurable.mul
      (havg.sub hp.stronglyMeasurable)).aestronglyMeasurable
  apply tendsto_iff_norm_sub_tendsto_zero.2
  have hsqrt : Tendsto (fun t : ℝ≥0 ↦ √(t : ℝ)) (𝓝[>] 0) (𝓝 0) := by
    have h : Continuous (fun t : ℝ≥0 ↦ √(t : ℝ)) := by fun_prop
    have h0 : √((0 : ℝ≥0) : ℝ) = 0 := by simp
    rw [← h0]
    exact (h.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  refine squeeze_zero' (Filter.Eventually.of_forall fun t ↦ norm_nonneg _) ?_
    (show Tendsto (fun t : ℝ≥0 ↦ C * (∫ x, ‖f x‖) * √(t : ℝ)) (𝓝[>] 0) (𝓝 0) by
      simpa using hsqrt.const_mul (C * ∫ x, ‖f x‖))
  filter_upwards [self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ≥0))] with t ht
  have ht' : (t : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast ht)
  have heq :
      (t : ℝ)⁻¹ * (∫ x, f x * (f x - avg t x)) - (1 / 2 * ∫ x, deriv f x ^ 2) =
        -((t : ℝ)⁻¹ * ∫ x, r t x) := by
    have hp (x : ℝ) : f x * (f x - avg t x) =
        (-(t : ℝ) / 2) * (f x * iteratedDeriv 2 f x) - r t x := by
      dsimp [r]
      ring
    simp_rw [hp]
    rw [integral_sub (hprod.const_mul _) (hr_int t), integral_const_mul, hparts]
    field_simp
    ring
  change ‖(t : ℝ)⁻¹ * (∫ x, f x * (f x - avg t x)) - (1 / 2 * ∫ x, deriv f x ^ 2)‖ ≤ _
  rw [heq, norm_neg, norm_mul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr t.coe_nonneg)]
  calc
    (t : ℝ)⁻¹ * ‖∫ x, r t x‖ ≤ (t : ℝ)⁻¹ * ∫ x, (C * √(t : ℝ) ^ 3) * ‖f x‖ :=
      mul_le_mul_of_nonneg_left
        (norm_integral_le_of_norm_le (hf_norm.const_mul _) (Filter.Eventually.of_forall (hbound t)))
        (inv_nonneg.mpr t.coe_nonneg)
    _ = C * (∫ x, ‖f x‖) * √(t : ℝ) := by
      rw [integral_const_mul, pow_succ, Real.sq_sqrt t.coe_nonneg]
      field_simp

end MathlibExt.Probability.DirichletFormWanted
