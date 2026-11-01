/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.NumberTheory.LSeries.Deriv

/-!
# Landau's theorem on integrals and Dirichlet series with nonnegative coefficients

Landau's theorem says that a Dirichlet series, or a Mellin-type integral, with nonnegative
coefficients has a singularity at the real point of its abscissa of convergence: it cannot be
continued holomorphically to any disc around that point.

Both versions reduce to the same observation: if `f` is holomorphic on `σ₀ < re s`, its
derivatives at real points `σ > σ₀` have the form `(-1) ^ k D(σ, k)` with `D(σ, k) ≥ 0`, and `f`
extends holomorphically to a disc around `σ₀`, then the Taylor series of `f` at some real
`σ₁ > σ₀` converges at some real `s < σ₀`. For nonnegative coefficients that series can be summed
term by term, which forces convergence at `s`.

## Main statements

* `MetaMathlibExt.exists_summable_taylor_of_holomorphic_extension`: the common Taylor-series
  step.
* `MetaMathlibExt.not_exists_holomorphic_extension_of_isGLB_integrableOn`: Landau's theorem for
  integrals `∫_1^∞ A(x) x ^ (-s-1) dx` with `A ≥ 0`.
* `LSeries.not_exists_holomorphic_extension_of_nonneg`: Landau's theorem for Dirichlet series
  with nonnegative coefficients, at the abscissa of absolute convergence.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace MetaMathlibExt

/-- The Taylor-series step of Landau's theorem. Let `f` be a function whose derivatives at real
points `σ > σ₀` are `(-1) ^ k D(σ, k)` for real `D(σ, k)`. If `g` is holomorphic on a disc around
`σ₀` and agrees with `f` on the part of the disc to the right of `σ₀`, then there are real
`σ₁ > σ₀` and `s < σ₀` with `∑ₖ (σ₁ - s) ^ k / k! D(σ₁, k)` summable. -/
theorem exists_summable_taylor_of_holomorphic_extension {f g : ℂ → ℂ} {σ₀ r : ℝ}
    (D : ℝ → ℕ → ℝ) (hD : ∀ σ : ℝ, σ₀ < σ → ∀ k, iteratedDeriv k f σ = (-1) ^ k * D σ k)
    (hr : 0 < r) (hg : DifferentiableOn ℂ g (Metric.ball (σ₀ : ℂ) r))
    (hfg : Set.EqOn g f (Metric.ball (σ₀ : ℂ) r ∩ {s : ℂ | σ₀ < s.re})) :
    ∃ σ₁ s : ℝ, σ₀ < σ₁ ∧ s < σ₀ ∧
      Summable fun k : ℕ => (σ₁ - s) ^ k / (k.factorial : ℝ) * D σ₁ k := by
  set σ₁ := σ₀ + r / 8 with hσ₁
  set s := σ₀ - r / 4 with hs
  refine ⟨σ₁, s, by linarith, by linarith, ?_⟩
  have hdistR : ∀ x y : ℝ, dist (x : ℂ) (y : ℂ) = |x - y| := by
    intro x y
    rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hd01 : dist (σ₁ : ℂ) (σ₀ : ℂ) = r / 8 := by
    rw [hdistR, abs_of_nonneg (by linarith)]
    ring
  have hball : Metric.ball (σ₁ : ℂ) (r / 8) ⊆ Metric.ball (σ₀ : ℂ) r ∩ {z : ℂ | σ₀ < z.re} := by
    intro z hz
    rw [Metric.mem_ball] at hz
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball]
      linarith [dist_triangle z (σ₁ : ℂ) (σ₀ : ℂ)]
    · have hlt : |z.re - σ₁| < r / 8 := by
        refine lt_of_le_of_lt ?_ hz
        rw [Complex.dist_eq]
        simpa using Complex.abs_re_le_norm (z - σ₁)
      have h2 := (abs_lt.mp hlt).1
      change σ₀ < z.re
      linarith
  have hEqf : g =ᶠ[𝓝 (σ₁ : ℂ)] f := by
    filter_upwards [Metric.ball_mem_nhds (σ₁ : ℂ) (show (0 : ℝ) < r / 8 by linarith)] with z hz
    exact hfg (hball hz)
  have hsub : Metric.ball (σ₁ : ℂ) (7 * r / 8) ⊆ Metric.ball (σ₀ : ℂ) r := by
    intro z hz
    rw [Metric.mem_ball] at hz ⊢
    linarith [dist_triangle z (σ₁ : ℂ) (σ₀ : ℂ)]
  have hmem : (s : ℂ) ∈ Metric.ball (σ₁ : ℂ) (7 * r / 8) := by
    rw [Metric.mem_ball, hdistR, abs_of_nonpos (by linarith)]
    linarith
  have htaylor := Complex.hasSum_taylorSeries_on_ball (hg.mono hsub) hmem
  have hfun : (fun k : ℕ => ((k.factorial : ℂ))⁻¹ • ((s : ℂ) - (σ₁ : ℂ)) ^ k •
      iteratedDeriv k g (σ₁ : ℂ)) =
      fun k : ℕ => (((σ₁ - s) ^ k / (k.factorial : ℝ) * D σ₁ k : ℝ) : ℂ) := by
    funext k
    rw [hEqf.iteratedDeriv_eq k, hD σ₁ (by linarith) k, smul_eq_mul, smul_eq_mul]
    have key : ((s : ℂ) - (σ₁ : ℂ)) ^ k * (-1 : ℂ) ^ k = ((σ₁ : ℂ) - (s : ℂ)) ^ k := by
      rw [← mul_pow]
      congr 1
      ring
    push_cast
    rw [div_eq_mul_inv, ← key]
    ring
  rw [hfun] at htaylor
  exact Complex.summable_ofReal.mp htaylor.summable

/-- The exponential series `∑ₖ (a log y) ^ k / k! = y ^ a`, for `y > 0`. -/
private theorem hasSum_rpow_log {y : ℝ} (hy : 0 < y) (a : ℝ) :
    HasSum (fun k : ℕ => a ^ k / (k.factorial : ℝ) * Real.log y ^ k) (y ^ a) := by
  have hexp : HasSum (fun k : ℕ => (a * Real.log y) ^ k / (k.factorial : ℝ))
      (Real.exp (a * Real.log y)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp _
  rw [Real.rpow_def_of_pos hy, mul_comm]
  refine hexp.congr_fun fun k => ?_
  rw [mul_pow]
  ring

/-- **Landau's theorem for integrals.** Let `A ≥ 0` on `[1, ∞)` and let `σ₀` be the infimum of
the real `s` for which `x ↦ A(x) / x ^ (s + 1)` is integrable on `(1, ∞)`. Then the function
`f(s) = ∫_1^∞ A(x) / x ^ (s + 1) dx`, holomorphic on `σ₀ < re s`, has a singularity at `σ₀`: no
holomorphic function on a disc around `σ₀` agrees with `f` on the part of the disc where
`σ₀ < re s`. -/
theorem not_exists_holomorphic_extension_of_isGLB_integrableOn
    (A : ℝ → ℝ) (hA : ∀ x : ℝ, 1 ≤ x → 0 ≤ A x) (σ₀ : ℝ)
    (hσ₀ : IsGLB {s : ℝ | IntegrableOn (fun x : ℝ => A x / x ^ (s + 1)) (Set.Ioi 1)} σ₀) :
    ¬ ∃ (r : ℝ) (g : ℂ → ℂ),
        0 < r ∧
        DifferentiableOn ℂ g (Metric.ball (σ₀ : ℂ) r) ∧
        Set.EqOn g (fun s : ℂ => ∫ x in Set.Ioi (1 : ℝ), (A x : ℂ) / (x : ℂ) ^ (s + 1))
          (Metric.ball (σ₀ : ℂ) r ∩ {s : ℂ | σ₀ < s.re}) := by
  rintro ⟨r, g, hr, hgdiff, hgeq⟩
  have hx0 : ∀ x : ℝ, x ∈ Set.Ioi (1 : ℝ) → (0 : ℝ) < x := fun x hx =>
    lt_trans zero_lt_one hx
  -- Strictly below any `σ > σ₀` the integral already converges at some exponent.
  have hex : ∀ σ : ℝ, σ₀ < σ → ∃ t : ℝ, t < σ ∧
      IntegrableOn (fun x : ℝ => A x / x ^ (t + 1)) (Set.Ioi 1) := by
    intro σ hσ
    by_contra hcon
    push Not at hcon
    have hlb : σ ∈ lowerBounds
        {u : ℝ | IntegrableOn (fun x : ℝ => A x / x ^ (u + 1)) (Set.Ioi 1)} := by
      intro u hu
      by_contra hlt
      exact hcon u (not_le.mp hlt) hu
    exact absurd (hσ₀.2 hlb) (not_le.mpr hσ)
  obtain ⟨t₀, -, ht₀⟩ := hex (σ₀ + 1) (by linarith)
  -- `A` is measurable on `(1, ∞)`, since some weighted version of it is integrable there.
  have hAmeas : AEStronglyMeasurable A (volume.restrict (Set.Ioi 1)) := by
    have hc : AEStronglyMeasurable (fun x : ℝ => x ^ (t₀ + 1))
        (volume.restrict (Set.Ioi (1 : ℝ))) := by
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      intro x hx
      exact (Real.continuousAt_rpow_const x (t₀ + 1)
        (Or.inl (hx0 x hx).ne')).continuousWithinAt
    refine (ht₀.1.mul hc).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hne : x ^ (t₀ + 1) ≠ 0 := (Real.rpow_pos_of_pos (hx0 x hx) _).ne'
    simp only [Pi.mul_apply]
    field_simp
  -- `(log x) ^ k` is dominated by `x ^ δ` on `[1, ∞)` for every `δ > 0`.
  have hlogbnd : ∀ (k : ℕ) (δ : ℝ), 0 < δ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : ℝ, 1 ≤ x → Real.log x ^ k ≤ C * x ^ δ := by
    intro k δ hδ
    obtain ⟨z, hz⟩ : ∃ z : ℝ, z = δ / (2 * (k + 1)) := ⟨_, rfl⟩
    have hzpos : 0 < z := by rw [hz]; positivity
    refine ⟨(1 / z) ^ k, by positivity, fun x hx1 => ?_⟩
    have hxp : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx1
    have h1 : Real.log x ^ k ≤ (x ^ z / z) ^ k :=
      pow_le_pow_left₀ (Real.log_nonneg hx1) (Real.log_le_rpow_div hxp.le hzpos) k
    have h2 : (x ^ z / z) ^ k = (1 / z) ^ k * x ^ (z * k) := by
      rw [div_pow, ← Real.rpow_natCast (x ^ z) k, ← Real.rpow_mul hxp.le, div_pow, one_pow]
      ring
    have h3 : x ^ (z * k) ≤ x ^ δ := by
      refine Real.rpow_le_rpow_of_exponent_le hx1 ?_
      rw [hz, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k), hδ.le]
    calc Real.log x ^ k ≤ (x ^ z / z) ^ k := h1
      _ = (1 / z) ^ k * x ^ (z * k) := h2
      _ ≤ (1 / z) ^ k * x ^ δ := mul_le_mul_of_nonneg_left h3 (by positivity)
  -- The real log-twisted integrals converge throughout the half-plane of convergence.
  have hIntR : ∀ (k : ℕ) (σ : ℝ), σ₀ < σ →
      IntegrableOn (fun x : ℝ => A x * Real.log x ^ k / x ^ (σ + 1)) (Set.Ioi 1) := by
    intro k σ hσ
    obtain ⟨t, htlt, ht⟩ := hex σ hσ
    obtain ⟨C, hC0, hC⟩ := hlogbnd k (σ - t) (by linarith)
    have hmeasF : AEStronglyMeasurable (fun x : ℝ => A x * Real.log x ^ k / x ^ (σ + 1))
        (volume.restrict (Set.Ioi 1)) := by
      have hc : AEStronglyMeasurable (fun x : ℝ => Real.log x ^ k / x ^ (σ + 1))
          (volume.restrict (Set.Ioi (1 : ℝ))) := by
        refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
        intro x hx
        have hxp : (0 : ℝ) < x := hx0 x hx
        exact (((Real.continuousAt_log hxp.ne').pow k).div
          (Real.continuousAt_rpow_const x (σ + 1) (Or.inl hxp.ne'))
          (Real.rpow_pos_of_pos hxp _).ne').continuousWithinAt
      refine (hAmeas.mul hc).congr ?_
      filter_upwards with x
      simp only [Pi.mul_apply]
      ring
    refine Integrable.mono' (ht.const_mul C) hmeasF ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx1 : (1 : ℝ) ≤ x := le_of_lt hx
    have hxp : (0 : ℝ) < x := hx0 x hx
    have hAx : 0 ≤ A x := hA x hx1
    have hsplit : A x * Real.log x ^ k / x ^ (σ + 1)
        = A x / x ^ (t + 1) * (Real.log x ^ k / x ^ (σ - t)) := by
      rw [show σ + 1 = t + 1 + (σ - t) by ring, Real.rpow_add hxp]
      have h1 : x ^ (t + 1) ≠ 0 := (Real.rpow_pos_of_pos hxp _).ne'
      have h2 : x ^ (σ - t) ≠ 0 := (Real.rpow_pos_of_pos hxp _).ne'
      field_simp
    have hdiv : Real.log x ^ k / x ^ (σ - t) ≤ C := by
      rw [div_le_iff₀ (Real.rpow_pos_of_pos hxp _)]
      exact hC x hx1
    have hAnn : 0 ≤ A x / x ^ (t + 1) := div_nonneg hAx (Real.rpow_pos_of_pos hxp _).le
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (mul_nonneg hAx
      (pow_nonneg (Real.log_nonneg hx1) k)) (Real.rpow_pos_of_pos hxp _).le), hsplit]
    calc A x / x ^ (t + 1) * (Real.log x ^ k / x ^ (σ - t))
        ≤ A x / x ^ (t + 1) * C := mul_le_mul_of_nonneg_left hdiv hAnn
      _ = C * (A x / x ^ (t + 1)) := by ring
  -- ... and so do their complex counterparts.
  have hIntC : ∀ (k : ℕ) (w : ℂ), σ₀ < w.re →
      IntegrableOn (fun x : ℝ => (A x : ℂ) * (Real.log x : ℂ) ^ k / (x : ℂ) ^ (w + 1))
        (Set.Ioi 1) := by
    intro k w hw
    have hmeasF : AEStronglyMeasurable
        (fun x : ℝ => (A x : ℂ) * (Real.log x : ℂ) ^ k / (x : ℂ) ^ (w + 1))
        (volume.restrict (Set.Ioi 1)) := by
      have hc : AEStronglyMeasurable (fun x : ℝ => (Real.log x : ℂ) ^ k / (x : ℂ) ^ (w + 1))
          (volume.restrict (Set.Ioi (1 : ℝ))) := by
        refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
        intro x hx
        have hxp : (0 : ℝ) < x := hx0 x hx
        have hne : ((x : ℂ) ^ (w + 1)) ≠ 0 :=
          Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hxp.ne'))
        refine ContinuousAt.continuousWithinAt (ContinuousAt.div ?_ ?_ hne)
        · exact ((Complex.continuous_ofReal.continuousAt).comp
            (Real.continuousAt_log hxp.ne')).pow k
        · exact Complex.continuousAt_ofReal_cpow_const x (w + 1) (Or.inr hxp.ne')
      refine ((Complex.continuous_ofReal.comp_aestronglyMeasurable hAmeas).mul hc).congr ?_
      filter_upwards with x
      simp only [Pi.mul_apply]
      ring
    refine Integrable.mono' (hIntR k w.re hw) hmeasF ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx1 : (1 : ℝ) ≤ x := le_of_lt hx
    rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
      Complex.norm_cpow_eq_rpow_re_of_pos (hx0 x hx), Complex.add_re, Complex.one_re,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hA x hx1),
      abs_of_nonneg (Real.log_nonneg hx1)]
  -- Differentiating the integrand in the parameter.
  have hcore : ∀ y : ℝ, 0 < y → ∀ c w : ℂ,
      HasDerivAt (fun z : ℂ => c / (y : ℂ) ^ (z + 1))
        (-((Real.log y : ℂ) * (c / (y : ℂ) ^ (w + 1)))) w := by
    intro y hy c w
    have hy0 : ((y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    have hg : HasDerivAt (fun z : ℂ => -(z + 1)) (-1) w :=
      ((hasDerivAt_id w).add_const (1 : ℂ)).neg
    have h2 : HasDerivAt (fun z : ℂ => c * ((y : ℝ) : ℂ) ^ (-(z + 1)))
        (c * (((y : ℝ) : ℂ) ^ (-(w + 1)) * Complex.log ((y : ℝ) : ℂ) * (-1))) w :=
      (hg.const_cpow (Or.inl hy0)).const_mul c
    have hfun : (fun z : ℂ => c * ((y : ℝ) : ℂ) ^ (-(z + 1)))
        = fun z : ℂ => c / ((y : ℝ) : ℂ) ^ (z + 1) := by
      funext z
      rw [Complex.cpow_neg, div_eq_mul_inv]
    rw [hfun] at h2
    convert h2 using 1
    rw [Complex.cpow_neg, ← Complex.ofReal_log hy.le, div_eq_mul_inv]
    ring
  set F : ℕ → ℂ → ℂ := fun k w =>
    ∫ x in Set.Ioi (1 : ℝ), (A x : ℂ) * (Real.log x : ℂ) ^ k / (x : ℂ) ^ (w + 1) with hF
  have hFderiv : ∀ (k : ℕ) (w : ℂ), σ₀ < w.re → HasDerivAt (F k) (-(F (k + 1) w)) w := by
    intro k w hw
    obtain ⟨σ₂, h2a, h2b⟩ := exists_between hw
    have hεpos : 0 < w.re - σ₂ := by linarith
    have hballre : ∀ z ∈ Metric.ball w (w.re - σ₂), σ₂ < z.re := by
      intro z hz
      rw [Metric.mem_ball, Complex.dist_eq] at hz
      have h := abs_lt.mp (lt_of_le_of_lt (by simpa using Complex.abs_re_le_norm (z - w)) hz)
      linarith [h.1]
    have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Set.Ioi (1 : ℝ)))
      (F := fun (z : ℂ) (x : ℝ) => (A x : ℂ) * (Real.log x : ℂ) ^ k / (x : ℂ) ^ (z + 1))
      (F' := fun (z : ℂ) (x : ℝ) =>
        -((A x : ℂ) * (Real.log x : ℂ) ^ (k + 1) / (x : ℂ) ^ (z + 1)))
      (x₀ := w) (bound := fun x : ℝ => A x * Real.log x ^ (k + 1) / x ^ (σ₂ + 1))
      (Metric.ball_mem_nhds w hεpos) ?_ (hIntC k w hw) ((hIntC (k + 1) w hw).1.neg) ?_
      (hIntR (k + 1) σ₂ h2a) ?_
    · have hval := hmain.2
      rw [integral_neg] at hval
      exact hval
    · filter_upwards [Metric.ball_mem_nhds w hεpos] with z hz
      exact (hIntC k z (lt_trans h2a (hballre z hz))).1
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx z hz
      have hx1 : (1 : ℝ) ≤ x := le_of_lt hx
      have hxp : (0 : ℝ) < x := hx0 x hx
      have hzre : σ₂ < z.re := hballre z hz
      rw [norm_neg, norm_div, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
        Complex.norm_cpow_eq_rpow_re_of_pos hxp, Complex.add_re, Complex.one_re,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hA x hx1),
        abs_of_nonneg (Real.log_nonneg hx1)]
      have hmono : x ^ (σ₂ + 1) ≤ x ^ (z.re + 1) :=
        Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      have hN : 0 ≤ A x * Real.log x ^ (k + 1) :=
        mul_nonneg (hA x hx1) (pow_nonneg (Real.log_nonneg hx1) _)
      have hposb : (0 : ℝ) < x ^ (σ₂ + 1) := Real.rpow_pos_of_pos hxp _
      gcongr
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx z _
      have h := hcore x (hx0 x hx) ((A x : ℂ) * (Real.log x : ℂ) ^ k) z
      have heq : -((Real.log x : ℂ) * ((A x : ℂ) * (Real.log x : ℂ) ^ k / (x : ℂ) ^ (z + 1)))
          = -((A x : ℂ) * (Real.log x : ℂ) ^ (k + 1) / (x : ℂ) ^ (z + 1)) := by ring
      rw [heq] at h
      exact h
  have hF0 : F 0 = fun z : ℂ => ∫ x in Set.Ioi (1 : ℝ), (A x : ℂ) / (x : ℂ) ^ (z + 1) := by
    funext z
    simp [hF]
  have hHopen : IsOpen {z : ℂ | σ₀ < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hiter : ∀ (k : ℕ) (z : ℂ), σ₀ < z.re → iteratedDeriv k (F 0) z = (-1) ^ k * F k z := by
    intro k
    induction k with
    | zero => intro z _; simp
    | succ n ih =>
      intro z hz
      have hev : iteratedDeriv n (F 0) =ᶠ[𝓝 z] fun y : ℂ => (-1 : ℂ) ^ n * F n y := by
        filter_upwards [hHopen.mem_nhds hz] with y hy using ih y hy
      rw [iteratedDeriv_succ, hev.deriv_eq,
        (HasDerivAt.const_mul ((-1 : ℂ) ^ n) (hFderiv n z hz)).deriv]
      ring
  -- The real values of the log-twisted integrals.
  set D : ℝ → ℕ → ℝ := fun σ k => ∫ x in Set.Ioi (1 : ℝ), A x * Real.log x ^ k / x ^ (σ + 1)
    with hD
  have hFreal : ∀ (σ : ℝ) (k : ℕ), F k (σ : ℂ) = (D σ k : ℂ) := by
    intro σ k
    rw [hF, hD, ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hcast : ((x : ℝ) : ℂ) ^ (((σ : ℝ) : ℂ) + 1) = (((x ^ (σ + 1) : ℝ)) : ℂ) := by
      rw [Complex.ofReal_cpow (hx0 x hx).le, Complex.ofReal_add, Complex.ofReal_one]
    simp only [hcast, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow]
  obtain ⟨σ₁, s, hσ₁gt, hslt, hGsummable⟩ :=
    exists_summable_taylor_of_holomorphic_extension (f := F 0) D
      (fun σ hσ k => by rw [hiter k σ (by simpa using hσ), hFreal]) hr hgdiff
      (fun z hz => (hgeq hz).trans (congrFun hF0 z).symm)
  have hsσ₁ : (0 : ℝ) < σ₁ - s := by linarith
  -- Interchanging sum and integral: the Taylor series is a series of nonnegative terms.
  have hpt : ∀ x ∈ Set.Ioi (1 : ℝ), HasSum
      (fun k : ℕ => (σ₁ - s) ^ k / (k.factorial : ℝ) * (A x * Real.log x ^ k / x ^ (σ₁ + 1)))
      (A x / x ^ (s + 1)) := by
    intro x hx
    have hxp : (0 : ℝ) < x := hx0 x hx
    have h2 := (hasSum_rpow_log hxp (σ₁ - s)).mul_right (A x / x ^ (σ₁ + 1))
    have hval : x ^ (σ₁ - s) * (A x / x ^ (σ₁ + 1)) = A x / x ^ (s + 1) := by
      rw [show σ₁ + 1 = (σ₁ - s) + (s + 1) by ring, Real.rpow_add hxp]
      have h3 : x ^ (σ₁ - s) ≠ 0 := (Real.rpow_pos_of_pos hxp _).ne'
      have h4 : x ^ (s + 1) ≠ 0 := (Real.rpow_pos_of_pos hxp _).ne'
      field_simp
    rw [hval] at h2
    exact h2.congr_fun fun k => by ring
  have haux_nonneg : ∀ (k : ℕ) (x : ℝ), x ∈ Set.Ioi (1 : ℝ) →
      0 ≤ (σ₁ - s) ^ k / (k.factorial : ℝ) * (A x * Real.log x ^ k / x ^ (σ₁ + 1)) := by
    intro k x hx
    have hx1 : (1 : ℝ) ≤ x := le_of_lt hx
    exact mul_nonneg (div_nonneg (pow_nonneg hsσ₁.le k) (Nat.cast_nonneg _))
      (div_nonneg (mul_nonneg (hA x hx1) (pow_nonneg (Real.log_nonneg hx1) k))
        (Real.rpow_pos_of_pos (hx0 x hx) _).le)
  have hDnn : ∀ k : ℕ, 0 ≤ D σ₁ k := fun k =>
    setIntegral_nonneg measurableSet_Ioi fun x hx =>
      div_nonneg (mul_nonneg (hA x (le_of_lt hx)) (pow_nonneg (Real.log_nonneg (le_of_lt hx)) k))
        (Real.rpow_pos_of_pos (hx0 x hx) _).le
  have hcoef_nonneg : ∀ k : ℕ, 0 ≤ (σ₁ - s) ^ k / (k.factorial : ℝ) * D σ₁ k := fun k =>
    mul_nonneg (div_nonneg (pow_nonneg hsσ₁.le k) (Nat.cast_nonneg _)) (hDnn k)
  have hint_a : ∀ k : ℕ, IntegrableOn
      (fun x : ℝ => (σ₁ - s) ^ k / (k.factorial : ℝ) * (A x * Real.log x ^ k / x ^ (σ₁ + 1)))
      (Set.Ioi 1) := fun k => (hIntR k σ₁ hσ₁gt).const_mul _
  have hmeas_a : ∀ k : ℕ, AEMeasurable (fun x : ℝ => ENNReal.ofReal
      ((σ₁ - s) ^ k / (k.factorial : ℝ) * (A x * Real.log x ^ k / x ^ (σ₁ + 1))))
      (volume.restrict (Set.Ioi (1 : ℝ))) :=
    fun k => ENNReal.measurable_ofReal.comp_aemeasurable (hint_a k).1.aemeasurable
  have hstep : ∀ k : ℕ, ∫⁻ x in Set.Ioi (1 : ℝ), ENNReal.ofReal
        ((σ₁ - s) ^ k / (k.factorial : ℝ) * (A x * Real.log x ^ k / x ^ (σ₁ + 1)))
      = ENNReal.ofReal ((σ₁ - s) ^ k / (k.factorial : ℝ) * D σ₁ k) := by
    intro k
    rw [hD, ← integral_const_mul]
    refine (ofReal_integral_eq_lintegral_ofReal (hint_a k) ?_).symm
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx using haux_nonneg k x hx
  have hL : ∫⁻ x in Set.Ioi (1 : ℝ), ENNReal.ofReal (A x / x ^ (s + 1))
      = ENNReal.ofReal (∑' k : ℕ, (σ₁ - s) ^ k / (k.factorial : ℝ) * D σ₁ k) := by
    rw [ENNReal.ofReal_tsum_of_nonneg hcoef_nonneg hGsummable]
    calc ∫⁻ x in Set.Ioi (1 : ℝ), ENNReal.ofReal (A x / x ^ (s + 1))
        = ∫⁻ x in Set.Ioi (1 : ℝ), ∑' k : ℕ, ENNReal.ofReal
            ((σ₁ - s) ^ k / (k.factorial : ℝ) * (A x * Real.log x ^ k / x ^ (σ₁ + 1))) := by
          refine lintegral_congr_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
          rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => haux_nonneg k x hx)
            (hpt x hx).summable, (hpt x hx).tsum_eq]
      _ = ∑' k : ℕ, ∫⁻ x in Set.Ioi (1 : ℝ), ENNReal.ofReal
            ((σ₁ - s) ^ k / (k.factorial : ℝ) * (A x * Real.log x ^ k / x ^ (σ₁ + 1))) :=
          lintegral_tsum hmeas_a
      _ = _ := tsum_congr hstep
  have hnn_int : 0 ≤ᵐ[volume.restrict (Set.Ioi (1 : ℝ))] fun x : ℝ => A x / x ^ (s + 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact div_nonneg (hA x (le_of_lt hx)) (Real.rpow_pos_of_pos (hx0 x hx) _).le
  have hmeas_final : AEStronglyMeasurable (fun x : ℝ => A x / x ^ (s + 1))
      (volume.restrict (Set.Ioi 1)) := by
    have hc : AEStronglyMeasurable (fun x : ℝ => (x ^ (s + 1))⁻¹)
        (volume.restrict (Set.Ioi (1 : ℝ))) := by
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      intro x hx
      exact ((Real.continuousAt_rpow_const x (s + 1) (Or.inl (hx0 x hx).ne')).inv₀
        (Real.rpow_pos_of_pos (hx0 x hx) _).ne').continuousWithinAt
    refine (hAmeas.mul hc).congr ?_
    filter_upwards with x
    simp only [Pi.mul_apply, div_eq_mul_inv]
  have hfinal : IntegrableOn (fun x : ℝ => A x / x ^ (s + 1)) (Set.Ioi 1) := by
    refine ⟨hmeas_final, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hnn_int, hL]
    exact ENNReal.ofReal_lt_top
  linarith [hσ₀.1 hfinal]

end MetaMathlibExt

namespace LSeries

/-- **Landau's theorem for Dirichlet series.** If `a n ≥ 0` for all `n` and the abscissa of
absolute convergence of `∑ a n n ^ (-s)` is the real number `σ₀`, then `LSeries a` has a
singularity at `σ₀`: no holomorphic function on a disc around `σ₀` agrees with `LSeries a` on the
part of the disc where `σ₀ < re s`. -/
theorem not_exists_holomorphic_extension_of_nonneg (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) {σ₀ : ℝ}
    (hσ₀ : abscissaOfAbsConv (fun n : ℕ => (a n : ℂ)) = σ₀) :
    ¬ ∃ (r : ℝ) (g : ℂ → ℂ), 0 < r ∧ DifferentiableOn ℂ g (Metric.ball (σ₀ : ℂ) r) ∧
      Set.EqOn g (LSeries fun n : ℕ => (a n : ℂ))
        (Metric.ball (σ₀ : ℂ) r ∩ {z : ℂ | σ₀ < z.re}) := by
  rintro ⟨r, g, hr, hgdiff, hgeq⟩
  have key : ∀ k : ℕ, (logMul^[k] fun n : ℕ => (a n : ℂ))
      = fun n : ℕ => (a n : ℂ) * (Real.log n : ℂ) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ p ih =>
      funext n
      rw [Function.iterate_succ_apply', ih]
      simp only [logMul, ← Complex.natCast_log]
      ring
  have habs : ∀ σ : ℝ, σ₀ < σ → abscissaOfAbsConv (fun n : ℕ => (a n : ℂ)) < ((σ : ℂ).re) := by
    intro σ hσ
    rw [hσ₀, Complex.ofReal_re]
    exact_mod_cast hσ
  -- the coefficients of the `k`-th derivative at the real point `σ`
  set cc : ℝ → ℕ → ℕ → ℝ := fun σ k n => if n = 0 then 0 else a n * Real.log n ^ k / (n : ℝ) ^ σ
    with hcc
  have hterm_c : ∀ (σ : ℝ) (k n : ℕ),
      term (fun m : ℕ => (a m : ℂ) * (Real.log m : ℂ) ^ k) (σ : ℂ) n = ((cc σ k n : ℝ) : ℂ) := by
    intro σ k n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hcc]
    · rw [term_of_ne_zero hn, hcc]
      simp only [hn, ↓reduceIte]
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg n)]
      push_cast
      ring
  have hc_nonneg : ∀ σ k n, 0 ≤ cc σ k n := by
    intro σ k n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hcc]
    · have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      simp only [hcc, hn, ↓reduceIte]
      exact div_nonneg (mul_nonneg (ha n) (pow_nonneg (Real.log_nonneg h1) k))
        (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hc_summable : ∀ σ : ℝ, σ₀ < σ → ∀ k, Summable (cc σ k) := by
    intro σ hσ k
    rw [← Complex.summable_ofReal]
    refine Summable.congr ?_ fun n => hterm_c σ k n
    rw [← key]
    refine LSeriesSummable_of_abscissaOfAbsConv_lt_re ?_
    rw [abscissaOfAbsConv_logPowMul]
    exact habs σ hσ
  set D : ℝ → ℕ → ℝ := fun σ k => ∑' n, cc σ k n with hD
  have hiter : ∀ σ : ℝ, σ₀ < σ → ∀ k,
      iteratedDeriv k (LSeries fun n : ℕ => (a n : ℂ)) (σ : ℂ) = (-1) ^ k * (D σ k : ℂ) := by
    intro σ hσ k
    rw [LSeries_iteratedDeriv k (habs σ hσ), key k, hD, Complex.ofReal_tsum]
    congr 1
    exact tsum_congr fun n => hterm_c σ k n
  obtain ⟨σ₁, x₀, hσ₁gt, hslt, hGsummable⟩ :=
    MetaMathlibExt.exists_summable_taylor_of_holomorphic_extension D hiter hr hgdiff hgeq
  have hsσ₁ : (0 : ℝ) < σ₁ - x₀ := by linarith
  set ww : ℕ → ℝ := fun n => if n = 0 then 0 else a n / (n : ℝ) ^ x₀ with hww
  have hterm_w : ∀ n : ℕ, term (fun m : ℕ => (a m : ℂ)) (x₀ : ℂ) n = ((ww n : ℝ) : ℂ) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hww]
    · rw [term_of_ne_zero hn, hww]
      simp only [hn, ↓reduceIte]
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg n)]
      push_cast
      ring
  have hw_nonneg : ∀ n, 0 ≤ ww n := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hww]
    · simp only [hww, hn, ↓reduceIte]
      exact div_nonneg (ha n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hpt : ∀ n : ℕ,
      HasSum (fun k : ℕ => (σ₁ - x₀) ^ k / (k.factorial : ℝ) * cc σ₁ k n) (ww n) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hcc, hww]
    · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have h2 := (MetaMathlibExt.hasSum_rpow_log hn0 (σ₁ - x₀)).mul_right (a n / (n : ℝ) ^ σ₁)
      have heq : (n : ℝ) ^ (σ₁ - x₀) * (a n / (n : ℝ) ^ σ₁) = ww n := by
        have hne1 : ((n : ℝ) ^ σ₁) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hn0 _)
        have hne2 : ((n : ℝ) ^ x₀) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hn0 _)
        simp only [hww, hn, ↓reduceIte]
        rw [Real.rpow_sub hn0]
        field_simp
      rw [heq] at h2
      refine h2.congr_fun fun k => ?_
      simp only [hcc, hn, ↓reduceIte]
      ring
  have hbound : ∀ N : ℕ, ∑ n ∈ Finset.range N, ww n
      ≤ ∑' k : ℕ, (σ₁ - x₀) ^ k / (k.factorial : ℝ) * D σ₁ k := by
    intro N
    have hsum := hasSum_sum (s := Finset.range N) (fun n _ => hpt n)
    have hle : ∀ k : ℕ, (∑ n ∈ Finset.range N, (σ₁ - x₀) ^ k / (k.factorial : ℝ) * cc σ₁ k n)
        ≤ (σ₁ - x₀) ^ k / (k.factorial : ℝ) * D σ₁ k := by
      intro k
      rw [← Finset.mul_sum, hD]
      refine mul_le_mul_of_nonneg_left ?_
        (div_nonneg (pow_nonneg hsσ₁.le k) (Nat.cast_nonneg _))
      exact Summable.sum_le_tsum _ (fun n _ => hc_nonneg σ₁ k n) (hc_summable σ₁ hσ₁gt k)
    rw [← hsum.tsum_eq]
    exact Summable.tsum_le_tsum hle hsum.summable hGsummable
  have hfinal : LSeriesSummable (fun n : ℕ => (a n : ℂ)) (x₀ : ℂ) :=
    Summable.congr (Complex.summable_ofReal.mpr (summable_of_sum_range_le hw_nonneg hbound))
      fun n => (hterm_w n).symm
  have hle := hfinal.abscissaOfAbsConv_le
  rw [hσ₀, Complex.ofReal_re] at hle
  exact absurd (by exact_mod_cast hle : σ₀ ≤ x₀) (not_le.mpr hslt)

end LSeries
