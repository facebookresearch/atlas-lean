/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Gamma
public import Mathlib.Probability.Moments.Variance
import MathlibExt.Probability.Distributions.Gamma

/-!
# Moments, scaling and upper tail of the gamma law

Mathlib's gamma law `gammaMeasure a r` has shape `a > 0` and rate `r > 0` (scale `1 / r`): its
density is `r ^ a / Γ(a) · x ^ (a - 1) e^{-r x}` on `x ≥ 0`. This file adds its real moments,
its behavior under scaling, and its upper tail in terms of the upper incomplete gamma function.

## Main results

* `Real.upperIncompleteGamma`: `Γ(a, x) = ∫ t in Ioi x, t ^ (a - 1) e^{-t}`, with
  `upperIncompleteGamma_zero` (`Γ(a, 0) = Γ(a)`), `upperIncompleteGamma_one`
  (`Γ(1, x) = e^{-x}`), the recurrence `upperIncompleteGamma_add_one`
  (`Γ(a + 1, x) = x ^ a e^{-x} + a Γ(a, x)`) and the closed form at natural shapes
  `upperIncompleteGamma_natCast_add_one` (`Γ(n + 1, x) = n! e^{-x} ∑_{k ≤ n} x ^ k / (k!)`).
* `ProbabilityTheory.integral_rpow_gammaMeasure`: `E[X ^ p] = Γ(a + p) / (Γ(a) r ^ p)` for
  `p > -a`; `integral_id_gammaMeasure` (mean `a / r`) and `variance_id_gammaMeasure`
  (variance `a / r ^ 2`).
* `ProbabilityTheory.gammaMeasure_map_const_mul`: if `X ~ Gamma(a, r)` and `c > 0` then
  `c X ~ Gamma(a, r / c)`.
* `ProbabilityTheory.gammaMeasure_real_Ioi`: `P(X > c) = Γ(a, r c) / Γ(a)` for `c ≥ 0`, and
  `gammaMeasure_real_Ioi_natCast_add_one`: `P(X > c) = e^{-r c} ∑_{k ≤ n} (r c) ^ k / (k!)` for
  the Erlang shape `a = n + 1`.

## References

* N. L. Johnson, S. Kotz and N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  2nd ed., Wiley (1994), ch. 17.
* NIST Digital Library of Mathematical Functions, §8.2 and §8.4 (incomplete gamma functions).
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal

namespace Real

/-- The upper incomplete gamma function `Γ(a, x) = ∫_x^∞ t ^ (a - 1) e^{-t} dt` (DLMF 8.2.2).
The domain used below is `a > 0` and `x ≥ 0`, where the integral converges. Outside it the
Bochner integral may be the junk value `0` (for `a ≤ 0`, `x = 0` the integrand is not
integrable). -/
noncomputable def upperIncompleteGamma (a x : ℝ) : ℝ :=
  ∫ t in Ioi x, t ^ (a - 1) * exp (-t)

/-- `Γ(a, 0) = Γ(a)` for `a > 0`. -/
theorem upperIncompleteGamma_zero {a : ℝ} (ha : 0 < a) : upperIncompleteGamma a 0 = Gamma a := by
  rw [upperIncompleteGamma, Gamma_eq_integral ha]
  simp_rw [mul_comm]

/-- `Γ(1, x) = e^{-x}`. -/
theorem upperIncompleteGamma_one (x : ℝ) : upperIncompleteGamma 1 x = exp (-x) := by
  simpa [upperIncompleteGamma] using integral_exp_neg_Ioi x

/-- The recurrence `Γ(a + 1, x) = x ^ a e^{-x} + a Γ(a, x)` for `a > 0` and `x ≥ 0`
(DLMF 8.8.2), from integration by parts. -/
theorem upperIncompleteGamma_add_one {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    upperIncompleteGamma (a + 1) x = x ^ a * exp (-x) + a * upperIncompleteGamma a x := by
  rcases hx.eq_or_lt with rfl | hx
  · rw [upperIncompleteGamma_zero (by positivity), upperIncompleteGamma_zero ha,
      Gamma_add_one ha.ne', zero_rpow ha.ne', zero_mul, zero_add]
  have h0 : IntegrableOn (fun t : ℝ => t ^ (a - 1) * exp (-t)) (Ioi x) := by
    simpa only [mul_comm] using
      (GammaIntegral_convergent ha).mono_set (Ioi_subset_Ioi hx.le)
  have h1 : IntegrableOn (fun t : ℝ => t ^ a * exp (-t)) (Ioi x) := by
    simpa only [add_sub_cancel_right, mul_comm] using
      (GammaIntegral_convergent (show 0 < a + 1 by positivity)).mono_set
        (Ioi_subset_Ioi hx.le)
  have hd : ∀ t ∈ Ioi x, HasDerivAt (fun t : ℝ => t ^ a * exp (-t))
      (a * (t ^ (a - 1) * exp (-t)) - t ^ a * exp (-t)) t := by
    intro t ht
    have ht0 : t ≠ 0 := (hx.trans ht).ne'
    convert! (hasDerivAt_rpow_const (Or.inl ht0)).mul
      ((hasDerivAt_id t).neg.exp) using 1
    simp only [Pi.neg_apply, id_eq]
    ring
  have hcont : ContinuousWithinAt (fun t : ℝ => t ^ a * exp (-t)) (Ici x) x := by
    simpa only [Pi.mul_def, Pi.neg_def, id_eq, Function.comp_def] using
      (((continuousAt_rpow_const x a (Or.inl hx.ne')).mul
        (Real.continuous_exp.continuousAt.comp continuousAt_id.neg)).continuousWithinAt)
  have hlim : Tendsto (fun t : ℝ => t ^ a * exp (-t)) atTop (nhds 0) := by
    simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero a 1 zero_lt_one
  have hi := integral_Ioi_of_hasDerivAt_of_tendsto hcont
    hd ((h0.const_mul a).sub h1) hlim
  simp only [integral_sub (h0.const_mul a) h1, integral_const_mul, zero_sub] at hi
  simp only [upperIncompleteGamma, add_sub_cancel_right]
  linarith

/-- The closed form at natural shapes (DLMF 8.4.8): for `x ≥ 0`,
`Γ(n + 1, x) = n! e^{-x} ∑_{k = 0}^{n} x ^ k / (k!)`. -/
theorem upperIncompleteGamma_natCast_add_one (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    upperIncompleteGamma (n + 1) x =
      Nat.factorial n * exp (-x) *
        ∑ k ∈ Finset.range (n + 1), x ^ k / Nat.factorial k := by
  induction n with
  | zero => simp [upperIncompleteGamma_one]
  | succ n ih =>
    have hn : (Nat.factorial n : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have hs : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    simp only [Nat.cast_succ]
    rw [upperIncompleteGamma_add_one (by positivity) hx, ih]
    conv_rhs => rw [Finset.sum_range_succ]
    have hp : x ^ (↑n + 1 : ℝ) = x ^ (n + 1 : ℕ) := by
      rw [← Nat.cast_add_one, rpow_natCast]
    rw [hp, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp
    ring

end Real

namespace ProbabilityTheory

open Real

/-- Real moments of the gamma law: for shape `a > 0`, rate `r > 0` and `p > -a`,
`E[X ^ p] = Γ(a + p) / (Γ(a) r ^ p)`. (The law is carried by `[0, ∞)`, so the values of
`x ^ p` for `x < 0` play no role.) -/
theorem integral_rpow_gammaMeasure {a r p : ℝ} (ha : 0 < a) (hr : 0 < r) (hp : -a < p) :
    ∫ x, x ^ p ∂gammaMeasure a r = Gamma (a + p) / (Gamma a * r ^ p) := by
  have hap : 0 < a + p := by linarith
  rw [integral_gammaMeasure_eq_integral_smul]
  simp_rw [toReal_gammaPDF ha hr, smul_eq_mul]
  have hd : (fun x => gammaPDFReal a r x * x ^ p) =
      (Ici 0).indicator
        (fun x => r ^ a / Gamma a * x ^ (a - 1) * exp (-(r * x)) * x ^ p) := by
    funext x
    by_cases hx : 0 ≤ x <;> simp [gammaPDFReal, hx]
  rw [hd, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]
  have hpow : (∫ x in Ioi 0,
      r ^ a / Gamma a * x ^ (a - 1) * exp (-(r * x)) * x ^ p) =
      ∫ x in Ioi 0, r ^ a / Gamma a * (x ^ (a + p - 1) * exp (-(r * x))) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [show a + p - 1 = (a - 1) + p by ring, rpow_add hx]
    ring
  rw [hpow, integral_const_mul, integral_rpow_mul_exp_neg_mul_Ioi hap hr,
    div_rpow zero_le_one hr.le, one_rpow, rpow_add hr]
  field_simp [(Gamma_pos_of_pos ha).ne', (rpow_pos_of_pos hr a).ne',
    (rpow_pos_of_pos hr p).ne']

private lemma integrable_rpow_gammaMeasure {a r p : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hp : -a < p) :
    Integrable (fun x : ℝ => x ^ p) (gammaMeasure a r) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_rpow_gammaMeasure ha hr hp]
  exact (div_pos (Gamma_pos_of_pos (by linarith))
    (mul_pos (Gamma_pos_of_pos ha) (rpow_pos_of_pos hr p))).ne'

/-- The mean of the gamma law with shape `a > 0` and rate `r > 0` is `a / r`. -/
theorem integral_id_gammaMeasure {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    ∫ x, x ∂gammaMeasure a r = a / r := by
  have hm := integral_rpow_gammaMeasure ha hr (p := 1) (by linarith)
  simp only [rpow_one, Gamma_add_one ha.ne'] at hm
  rw [hm]
  field_simp [(Gamma_pos_of_pos ha).ne']

/-- The second moment of the gamma law with shape `a > 0` and rate `r > 0` is
`a (a + 1) / r ^ 2`. -/
theorem integral_sq_gammaMeasure {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    ∫ x, x ^ 2 ∂gammaMeasure a r = a * (a + 1) / r ^ 2 := by
  have hm := integral_rpow_gammaMeasure ha hr (p := 2) (by linarith)
  simp only [rpow_two] at hm
  rw [hm, show a + 2 = (a + 1) + 1 by ring,
    Gamma_add_one (by linarith : a + 1 ≠ 0), Gamma_add_one ha.ne']
  field_simp [(Gamma_pos_of_pos ha).ne']

/-- The gamma law has finite second moment. -/
theorem memLp_id_gammaMeasure {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    MemLp id 2 (gammaMeasure a r) := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).2
  simpa only [id_eq, rpow_two] using
    integrable_rpow_gammaMeasure ha hr (p := 2) (by linarith)

/-- The variance of the gamma law with shape `a > 0` and rate `r > 0` is `a / r ^ 2`. -/
theorem variance_id_gammaMeasure {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    variance id (gammaMeasure a r) = a / r ^ 2 := by
  let := isProbabilityMeasure_gammaMeasure ha hr
  rw [variance_eq_sub (memLp_id_gammaMeasure ha hr)]
  change (∫ x, x ^ 2 ∂gammaMeasure a r) - (∫ x, x ∂gammaMeasure a r) ^ 2 = _
  rw [integral_sq_gammaMeasure ha hr, integral_id_gammaMeasure ha hr]
  field_simp
  ring

private lemma gammaPDFReal_div_scale {a r c : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hc : 0 < c) (x : ℝ) :
    gammaPDFReal a r (x / c) / c = gammaPDFReal a (r / c) x := by
  by_cases hx : 0 ≤ x
  · simp only [gammaPDFReal, ite_eq_left hx, ite_eq_left (div_nonneg hx hc.le)]
    rw [div_rpow hx hc.le, div_rpow hr.le hc.le,
      show r * (x / c) = r / c * x by ring, rpow_sub hc, rpow_one]
    field_simp [hc.ne', (rpow_pos_of_pos hc a).ne', (Gamma_pos_of_pos ha).ne']
  · have hxc : ¬0 ≤ x / c := not_le.mpr (div_neg_of_neg_of_pos (lt_of_not_ge hx) hc)
    simp [gammaPDFReal, hx, hxc]

/-- Scaling a gamma variable by `c > 0` keeps its shape and divides its rate by `c`:
`c X ~ Gamma(a, r / c)` when `X ~ Gamma(a, r)`. -/
theorem gammaMeasure_map_const_mul {a r c : ℝ} (ha : 0 < a) (hr : 0 < r) (hc : 0 < c) :
    (gammaMeasure a r).map (fun x => c * x) = gammaMeasure a (r / c) := by
  have hmul : Measurable (fun x : ℝ => c * x) := by fun_prop
  have hpdf : Measurable (fun y : ℝ => gammaPDF a r (y / c)) :=
    (measurable_gammaPDF a r).comp (by fun_prop : Measurable (fun y : ℝ => y / c))
  ext s hs
  calc
    (gammaMeasure a r).map (fun x => c * x) s =
        ∫⁻ x, ((fun x : ℝ => c * x) ⁻¹' s).indicator (gammaPDF a r) x := by
      rw [Measure.map_apply hmul hs, gammaMeasure,
        withDensity_apply _ (hmul hs), lintegral_indicator (hmul hs)]
    _ = ∫⁻ x, s.indicator (fun y => gammaPDF a r (y / c)) (c * x) := by
      apply lintegral_congr
      intro x
      by_cases hx : c * x ∈ s <;> simp [hx, hc.ne']
    _ = ∫⁻ x, s.indicator (fun y => gammaPDF a r (y / c)) x
        ∂volume.map (fun x => c * x) := by
      rw [lintegral_map (hpdf.indicator hs) hmul]
    _ = ∫⁻ x in s, gammaPDF a (r / c) x := by
      rw [Real.map_volume_mul_left hc.ne', abs_of_pos (inv_pos.mpr hc),
        lintegral_smul_measure, smul_eq_mul,
        ← lintegral_const_mul _
          (hpdf.indicator hs)]
      rw [← lintegral_indicator hs]
      apply lintegral_congr
      intro x
      by_cases hx : x ∈ s
      · simp only [indicator_of_mem hx, gammaPDF]
        rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le), inv_mul_eq_div,
          gammaPDFReal_div_scale ha hr hc]
      · simp [indicator_of_notMem hx]
    _ = gammaMeasure a (r / c) s := by
      rw [gammaMeasure, withDensity_apply _ hs]

/-- The upper tail of the gamma law: `P(X > c) = Γ(a, r c) / Γ(a)` for `c ≥ 0`. -/
theorem gammaMeasure_real_Ioi {a r c : ℝ} (ha : 0 < a) (hr : 0 < r) (hc : 0 ≤ c) :
    (gammaMeasure a r).real (Ioi c) = upperIncompleteGamma a (r * c) / Gamma a := by
  have hd : (gammaMeasure a r).real (Ioi c) = ∫ x in Ioi c, gammaPDFReal a r x := by
    rw [gammaMeasure, measureReal_def, withDensity_apply _ measurableSet_Ioi]
    exact (integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ fun x => gammaPDFReal_nonneg ha hr x)
      (measurable_gammaPDFReal a r).aestronglyMeasurable).symm
  rw [hd]
  have he : ∫ x in Ioi c, gammaPDFReal a r x =
      ∫ x in Ioi c, (r / Gamma a) * ((r * x) ^ (a - 1) * exp (-(r * x))) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hx0 : 0 ≤ x := hc.trans hx.le
    change gammaPDFReal a r x =
      (r / Gamma a) * ((r * x) ^ (a - 1) * exp (-(r * x)))
    rw [gammaPDFReal, ite_eq_left hx0, mul_rpow hr.le hx0, rpow_sub hr _ _, rpow_one]
    field_simp
  rw [he, integral_const_mul,
    integral_comp_mul_left_Ioi (fun t : ℝ => t ^ (a - 1) * exp (-t)) c hr]
  simp only [smul_eq_mul, upperIncompleteGamma]
  field_simp

/-- The Erlang tail: for shape `n + 1`, `P(X > c) = e^{-r c} ∑_{k = 0}^{n} (r c) ^ k / (k!)`
when `c ≥ 0`. -/
theorem gammaMeasure_real_Ioi_natCast_add_one (n : ℕ) {r c : ℝ} (hr : 0 < r) (hc : 0 ≤ c) :
    (gammaMeasure (n + 1) r).real (Ioi c) =
      exp (-(r * c)) * ∑ k ∈ Finset.range (n + 1), (r * c) ^ k / Nat.factorial k := by
  have hn : (Nat.factorial n : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [gammaMeasure_real_Ioi (by positivity) hr hc,
    upperIncompleteGamma_natCast_add_one n (mul_nonneg hr.le hc),
    Gamma_nat_eq_factorial]
  field_simp

end ProbabilityTheory
