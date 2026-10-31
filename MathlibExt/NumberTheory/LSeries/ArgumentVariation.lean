/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Analysis.Asymptotics.Defs
import MathlibExt.Analysis.SpecialFunctions.Gamma.Binet
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The variation of the argument along the path `2 → 2 + iT → 1/2 + iT`

In the Riemann–von Mangoldt formula the number of zeros of `ξ` up to height `T` is read off from
the change of argument of the factors `s - 1`, `π^{-s/2}`, `Γ(s/2 + 1)` and `ζ(s)` along the
polygonal path from `2` to `2 + iT` to `1/2 + iT`. We define this variation through the integral
of the logarithmic derivative, which avoids the branch cuts of `Complex.arg`, and evaluate it for
the elementary factors.

## Main definitions

* `argVariationToCriticalLine f T`: `Im ∫ f'/f` along the segments `2 → 2 + iT → 1/2 + iT`.

## Main statements

* `DifferentiableOn.apply_eq_mul_exp_integral_logDeriv`: integrating the logarithmic derivative
  of a nonvanishing holomorphic function along an affine path exponentiates to the ratio of the
  endpoint values.
* `argVariationToCriticalLine_sub_one_sub_isBigO`: for `s - 1` the variation is `π/2 + O(1/T)`.
* `argVariationToCriticalLine_pi_cpow`: for `π^{-s/2}` it is exactly `-(T/2) log π`.
* `argVariationToCriticalLine_Gamma_sub_isBigO`: for `Γ(s/2 + 1)` it is
  `(T/2) log (T/2) - T/2 + 3π/8 + O(1/T)`, by Stirling's formula.
-/

@[expose] public section

open Complex Filter Asymptotics Set

/-- **The argument variation along `2 → 2 + iT → 1/2 + iT`**: `Im ∫ f'(s)/f(s) ds` along the
vertical segment from `2` to `2 + iT` followed by the horizontal segment from `2 + iT` to
`1/2 + iT`. When `f` is holomorphic and nonvanishing near the path, this is the continuous change
of `arg f` along it. Where `f` vanishes on the path the value carries no meaning. -/
noncomputable def argVariationToCriticalLine (f : ℂ → ℂ) (T : ℝ) : ℝ :=
  (∫ y in (0 : ℝ)..T, logDeriv f (2 + y * I) * I).im +
    (∫ x in (2 : ℝ)..(1 / 2), logDeriv f (x + T * I)).im

/-- Integrating the logarithmic derivative of a nonvanishing holomorphic function `f` along an
affine path `p` with constant velocity `d` exponentiates to the ratio of the endpoint values:
`f (p b) = f (p a) exp (∫_a^b f'(p t)/f(p t) d dt)`. -/
theorem DifferentiableOn.apply_eq_mul_exp_integral_logDeriv {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hf0 : ∀ z ∈ U, f z ≠ 0) {p : ℝ → ℂ} {d : ℂ}
    (hp : ∀ t, HasDerivAt p d t) {a b : ℝ} (hab : a ≤ b) (hseg : ∀ t ∈ Icc a b, p t ∈ U) :
    f (p b) = f (p a) * Complex.exp (∫ t in a..b, logDeriv f (p t) * d) := by
  have hpc : Continuous p := continuous_iff_continuousAt.2 fun t => (hp t).continuousAt
  have hVo : IsOpen (p ⁻¹' U) := hU.preimage hpc
  have hψ : ContinuousOn (logDeriv f) U :=
    ((hf.analyticOnNhd hU).deriv.continuousOn.div hf.continuousOn hf0 :
      ContinuousOn (fun z => _root_.deriv f z / f z) U)
  set g : ℝ → ℂ := fun t => logDeriv f (p t) * d with hg
  have hgc : ContinuousOn g (p ⁻¹' U) :=
    (hψ.comp hpc.continuousOn (fun t ht => ht)).mul continuousOn_const
  have hsub : Icc a b ⊆ p ⁻¹' U := fun t ht => hseg t ht
  have hint : ∀ t ∈ Icc a b, IntervalIntegrable g MeasureTheory.volume a t := by
    intro t ht
    refine (hgc.mono fun s hs => hsub ?_).intervalIntegrable
    rw [uIcc_of_le ht.1] at hs
    exact ⟨hs.1, hs.2.trans ht.2⟩
  set h : ℝ → ℂ := fun t => ∫ s in a..t, g s with hh_def
  have hh : ∀ t ∈ Icc a b, HasDerivAt h (g t) t := fun t ht =>
    intervalIntegral.integral_hasDerivAt_right (hint t ht)
      (hgc.stronglyMeasurableAtFilter hVo t (hsub ht))
      (hgc.continuousAt (hVo.mem_nhds (hsub ht)))
  set φ : ℝ → ℂ := fun t => f (p t) * Complex.exp (-h t) with hφ_def
  have hφ : ∀ t ∈ Icc a b, HasDerivAt φ 0 t := by
    intro t ht
    have hft : HasDerivAt f (_root_.deriv f (p t)) (p t) :=
      (hf.differentiableAt (hU.mem_nhds (hseg t ht))).hasDerivAt
    have h2 : HasDerivAt φ (_root_.deriv f (p t) * d * Complex.exp (-h t) +
        f (p t) * (Complex.exp (-h t) * -g t)) t := (hft.comp t (hp t)).mul ((hh t ht).neg.cexp)
    refine h2.congr_deriv ?_
    have := hf0 _ (hseg t ht)
    simp only [hg, logDeriv_apply]
    field_simp
    ring
  have hconst := constant_of_has_deriv_right_zero (f := φ) (a := a) (b := b)
    (fun t ht => (hφ t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hφ t (Ico_subset_Icc_self ht)).hasDerivWithinAt) b ⟨hab, le_rfl⟩
  simp only [hφ_def, hh_def, intervalIntegral.integral_same, neg_zero, exp_zero,
    mul_one] at hconst
  calc f (p b) = f (p b) * Complex.exp (-h b) * Complex.exp (h b) := by
        rw [mul_assoc, ← exp_add]; simp
    _ = _ := by rw [hconst]

/-- The variation of the argument of `s - 1` along `2 → 2 + iT → 1/2 + iT` is
`π/2 + O(1/T)` as `T → ∞`. -/
theorem argVariationToCriticalLine_sub_one_sub_isBigO :
    (fun T : ℝ => argVariationToCriticalLine (fun s : ℂ => s - 1) T - Real.pi / 2) =O[atTop]
      (fun T : ℝ => 1 / T) := by
  have key : ∀ T : ℝ, 0 < T → argVariationToCriticalLine (fun s : ℂ => s - 1) T
      = Real.arctan T + (Real.arctan (1 / T) + Real.arctan (1 / (2 * T))) := by
    intro T hT
    have hld : ∀ s : ℂ, logDeriv (fun s : ℂ => s - 1) s = 1 / (s - 1) := by
      intro s; simp [logDeriv_apply, div_eq_mul_inv]
    unfold argVariationToCriticalLine
    simp only [hld]
    have hne1 : ∀ y : ℝ, (1 : ℂ) + y * I ≠ 0 := by
      intro y h; have := congrArg re h; simp at this
    have hne2 : ∀ x : ℝ, (x : ℂ) - 1 + T * I ≠ 0 := by
      intro x h; exact hT.ne' (by simpa using congrArg im h)
    have hc1 : Continuous fun y : ℝ => 1 / ((2 : ℂ) + y * I - 1) * I := by
      have : (fun y : ℝ => 1 / ((2 : ℂ) + y * I - 1) * I) = fun y : ℝ => I / (1 + y * I) := by
        funext y; rw [show (2 : ℂ) + y * I - 1 = 1 + y * I by ring]; ring
      rw [this]
      exact continuous_const.div (by fun_prop) hne1
    have hc2 : Continuous fun x : ℝ => 1 / ((x : ℂ) + T * I - 1) := by
      have : (fun x : ℝ => 1 / ((x : ℂ) + T * I - 1)) =
          fun x : ℝ => 1 / ((x : ℂ) - 1 + T * I) := by
        funext x; ring_nf
      rw [this]
      exact continuous_const.div (by fun_prop) hne2
    have h1 : (∫ y in (0:ℝ)..T, 1 / ((2 : ℂ) + y * I - 1) * I).im
        = ∫ y in (0:ℝ)..T, (1 / ((2 : ℂ) + y * I - 1) * I).im :=
      (intervalIntegral.intervalIntegral_im (hc1.intervalIntegrable 0 T)).symm
    have h2 : (∫ x in (2:ℝ)..(1/2), 1 / ((x : ℂ) + T * I - 1)).im
        = ∫ x in (2:ℝ)..(1/2), (1 / ((x : ℂ) + T * I - 1)).im :=
      (intervalIntegral.intervalIntegral_im (hc2.intervalIntegrable _ _)).symm
    rw [h1, h2]
    have e1 : ∀ y : ℝ, im (1 / ((2 : ℂ) + y * I - 1) * I) = 1 / (1 + y ^ 2) := by
      intro y
      rw [show (2 : ℂ) + y * I - 1 = 1 + y * I by ring]
      simp [normSq]
      ring
    have e2 : ∀ x : ℝ, im (1 / ((x : ℂ) + T * I - 1)) = -T / ((x - 1) ^ 2 + T ^ 2) := by
      intro x
      rw [show (x : ℂ) + T * I - 1 = ((x - 1 : ℝ) : ℂ) + T * I by push_cast; ring]
      simp [normSq]
      ring
    simp only [e1, e2, integral_one_div_one_add_sq, Real.arctan_zero, sub_zero]
    congr 1
    have hderiv : ∀ x ∈ uIcc (2 : ℝ) (1 / 2),
        HasDerivAt (fun x => -Real.arctan ((x - 1) / T)) (-T / ((x - 1) ^ 2 + T ^ 2)) x := by
      intro x _
      have h' : HasDerivAt (fun x => -Real.arctan ((x - 1) / T))
          (-(1 / (1 + ((x - 1) / T) ^ 2) * (1 / T))) x :=
        (((hasDerivAt_id x).sub_const 1).div_const T |>.arctan).neg
      refine h'.congr_deriv ?_
      field_simp
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      ((Continuous.continuousOn (continuous_const.div (by fun_prop)
        (fun x => by positivity))).intervalIntegrable)]
    have ha : (1 / 2 - 1) / T = -(1 / (2 * T)) := by field_simp; ring
    have hb : ((2 : ℝ) - 1) / T = 1 / T := by norm_num
    rw [ha, hb, Real.arctan_neg]
    ring
  have harctan_lt : ∀ y : ℝ, 0 < y → Real.arctan y < y := by
    intro y hy
    rcases le_or_gt (Real.pi / 2) y with h | h
    · exact (Real.arctan_lt_pi_div_two y).trans_le h
    · have h0 : 0 < Real.arctan y := Real.arctan_pos.mpr hy
      have ht := Real.lt_tan h0 (Real.arctan_lt_pi_div_two y)
      rwa [Real.tan_arctan] at ht
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_gt_atTop 0] with T hT
  rw [key T hT, one_div T, Real.arctan_inv_of_pos hT]
  have hpos : 0 < 1 / (2 * T) := by positivity
  have h1 := harctan_lt _ hpos
  have h0 := Real.arctan_pos.mpr hpos
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hT),
    show Real.arctan T + (Real.pi / 2 - Real.arctan T + Real.arctan (1 / (2 * T))) - Real.pi / 2
      = Real.arctan (1 / (2 * T)) by ring, abs_of_pos h0]
  have : 1 / (2 * T) ≤ T⁻¹ := by
    rw [one_div, mul_inv]; nlinarith [inv_pos.mpr hT]
  linarith

/-- The variation of the argument of `π^{-s/2}` along `2 → 2 + iT → 1/2 + iT` is exactly
`-(T/2) log π`. -/
theorem argVariationToCriticalLine_pi_cpow (T : ℝ) :
    argVariationToCriticalLine (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2)) T =
      -(T / 2) * Real.log Real.pi := by
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hL : ∀ s : ℂ, logDeriv (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2)) s
      = -(Real.log Real.pi : ℂ) / 2 := by
    intro s
    have hd : HasDerivAt (fun s : ℂ => -s / 2) (-1 / 2) s := by
      simpa using ((hasDerivAt_id s).neg.div_const 2)
    have h := hd.const_cpow (c := (Real.pi : ℂ)) (Or.inl hπ)
    rw [logDeriv_apply, h.deriv]
    have hne : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := by
      rw [Ne, cpow_eq_zero_iff]; tauto
    rw [← ofReal_log Real.pi_pos.le]
    field_simp
  unfold argVariationToCriticalLine
  simp only [hL, intervalIntegral.integral_const]
  simp
  ring

private lemma int_eq_zero_of_abs_sub_le {x : ℝ} {m : ℤ} (h : |x - 2 * Real.pi * m| ≤ 1 / 2)
    (hx : |x| ≤ 1) : m = 0 := by
  by_contra hm
  have h1 : (1 : ℝ) ≤ |(m : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hm
  have hpi := Real.two_le_pi
  have e : |2 * Real.pi * (m : ℝ)| ≤ 3 / 2 := by
    calc |2 * Real.pi * (m : ℝ)| = |x - (x - 2 * Real.pi * m)| := by ring_nf
      _ ≤ |x| + |x - 2 * Real.pi * m| := abs_sub _ _
      _ ≤ 3 / 2 := by linarith
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at e
  nlinarith

/-- A continuous real function that starts within `1/2` of `0` and always stays within `1/2`
of the lattice `2πℤ` stays within `1/2` of `0`. -/
private lemma abs_le_half_of_near_lattice {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (ha : |f a| ≤ 1 / 2)
    (hlat : ∀ t ∈ Icc a b, ∃ m : ℤ, |f t - 2 * Real.pi * m| ≤ 1 / 2) :
    ∀ t ∈ Icc a b, |f t| ≤ 1 / 2 := by
  intro t ht
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨m, hm⟩ := hlat t ht
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
    linarith
  have hbig : 1 ≤ |f t| := by
    by_contra hsmall
    rw [not_le] at hsmall
    exact hm0 (int_eq_zero_of_abs_sub_le hm hsmall.le)
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
  have hfc := hf.mono hsub
  have key : ∃ s ∈ Icc a t, |f s| = 1 := by
    rcases le_or_gt 0 (f t) with hpos | hneg
    · rw [abs_of_nonneg hpos] at hbig
      obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc ht.1 hfc
        (show (1 : ℝ) ∈ Icc (f a) (f t) from ⟨by linarith [(abs_le.1 ha).2], hbig⟩)
      exact ⟨s, hs, by rw [hfs]; norm_num⟩
    · rw [abs_of_neg hneg] at hbig
      obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc' ht.1 hfc
        (show (-1 : ℝ) ∈ Icc (f t) (f a) from ⟨by linarith, by linarith [(abs_le.1 ha).1]⟩)
      exact ⟨s, hs, by rw [hfs]; norm_num⟩
  obtain ⟨s, hs, hfs⟩ := key
  obtain ⟨m', hm'⟩ := hlat s (hsub hs)
  have := int_eq_zero_of_abs_sub_le hm' hfs.le
  subst this
  simp at hm'
  linarith

/-- `‖log (z + 1) - log z - 1/z‖ ≤ 1/‖z‖²` for `Re z > 0`. -/
theorem Complex.norm_log_add_one_sub_log_sub_inv_le {z : ℂ} (hz : 0 < z.re) :
    ‖log (z + 1) - log z - 1 / z‖ ≤ 1 / ‖z‖ ^ 2 := by
  have hz0 : z ≠ 0 := by
    intro h; simp [h] at hz
  have hslit : ∀ t : ℝ, 0 ≤ t → z + t ∈ slitPlane := fun t ht =>
    mem_slitPlane_iff.2 (Or.inl (by simp; linarith))
  have hnorm : ∀ t : ℝ, 0 ≤ t → ‖z‖ ≤ ‖z + t‖ := by
    intro t ht
    have h1 : ‖z‖ ^ 2 ≤ ‖z + t‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm, normSq_apply, normSq_apply]
      simp
      nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h1
  have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hne : ∀ t : ℝ, 0 ≤ t → z + t ≠ 0 := fun t ht h => by
    have := hnorm t ht
    rw [h, norm_zero] at this
    linarith
  have hcont : ContinuousOn (fun t : ℝ => 1 / (z + t)) (uIcc 0 1) := by
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    exact hne t ht.1
  have hftc : log (z + 1) - log z = ∫ t in (0 : ℝ)..1, 1 / (z + t) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t : ℝ => log (z + t))]
    · simp
    · intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      simpa using ((hasDerivAt_id t).ofReal_comp.const_add z).clog_real (hslit t ht.1)
    · exact hcont.intervalIntegrable
  have hrw : log (z + 1) - log z - 1 / z = ∫ t in (0 : ℝ)..1, (1 / (z + t) - 1 / z) := by
    rw [intervalIntegral.integral_sub hcont.intervalIntegrable (by simp), hftc]
    simp
  rw [hrw]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (C := 1 / ‖z‖ ^ 2) (f := fun t : ℝ => 1 / (z + t) - 1 / z) ?_
  · simpa using hb
  · intro t ht
    rw [uIoc_of_le zero_le_one] at ht
    have ht0 : 0 ≤ t := ht.1.le
    have h1 := hnorm t ht0
    have h2 := hne t ht0
    rw [div_sub_div _ _ (hne t ht0) hz0, norm_div, norm_mul,
      show (1 * z - (z + (t : ℂ)) * 1) = -(t : ℂ) by ring, norm_neg, norm_real,
      Real.norm_eq_abs, abs_of_nonneg ht0, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [ht.2, mul_le_mul_of_nonneg_left h1 hzpos.le]

/-- One step of the Stirling main term: replacing `z` by `z + 1` changes
`(z - 1/2) log z - z + log (2π) / 2` by `log z + O(1/‖z‖)`. -/
private lemma norm_stirling_step {z : ℂ} (hz : 0 < z.re) (hz1 : 1 ≤ ‖z‖) :
    ‖((z + 1 - 1 / 2) * log (z + 1) - (z + 1) + 1 / 2 * log (2 * Real.pi)) -
        ((z - 1 / 2) * log z - z + 1 / 2 * log (2 * Real.pi)) - log z‖ ≤ 2 / ‖z‖ := by
  have hz0 : z ≠ 0 := by
    intro h; simp [h] at hz
  have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hρ := Complex.norm_log_add_one_sub_log_sub_inv_le hz
  set ρ := log (z + 1) - log z - 1 / z with hρdef
  have hid : ((z + 1 - 1 / 2) * log (z + 1) - (z + 1) + 1 / 2 * log (2 * Real.pi)) -
        ((z - 1 / 2) * log z - z + 1 / 2 * log (2 * Real.pi)) - log z =
      (z + 1 / 2) * ρ + 1 / (2 * z) := by
    rw [hρdef]
    field_simp
    ring
  rw [hid]
  have h12 : ‖z + 1 / 2‖ ≤ ‖z‖ + 1 / 2 := (norm_add_le _ _).trans (by norm_num)
  have h3 : ‖1 / (2 * z)‖ = 1 / (2 * ‖z‖) := by
    rw [norm_div, norm_mul]; norm_num
  calc ‖(z + 1 / 2) * ρ + 1 / (2 * z)‖ ≤ ‖z + 1 / 2‖ * ‖ρ‖ + ‖1 / (2 * z)‖ := by
        rw [← norm_mul]; exact norm_add_le _ _
    _ ≤ (‖z‖ + 1 / 2) * (1 / ‖z‖ ^ 2) + 1 / (2 * ‖z‖) := by
        rw [h3]; gcongr
    _ ≤ 2 / ‖z‖ := by
        rw [show (‖z‖ + 1 / 2) * (1 / ‖z‖ ^ 2) + 1 / (2 * ‖z‖) =
          (3 * ‖z‖ + 1) / (2 * ‖z‖ ^ 2) by field_simp; ring,
          div_le_div_iff₀ (by positivity) hzpos]
        nlinarith

private lemma differentiableAt_Gamma_half_add_one {s : ℂ} (hs : -2 < s.re) :
    DifferentiableAt ℂ (fun s : ℂ => Gamma (s / 2 + 1)) s := by
  have hre : 0 < (s / 2 + 1).re := by simp; linarith
  refine (differentiableAt_Gamma _ fun m h => ?_).comp s (by fun_prop)
  rw [h] at hre
  simp at hre
  linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

private lemma im_logDeriv_Gamma_half_add_one {x : ℝ} (hx : 0 < x) :
    (logDeriv (fun s : ℂ => Gamma (s / 2 + 1)) x).im = 0 := by
  have h1 := (differentiableAt_Gamma_half_add_one (s := (x : ℂ))
    (by simp; linarith)).hasDerivAt.comp_ofReal
  have hfun : (fun y : ℝ => Gamma ((y : ℂ) / 2 + 1)) =
      fun y : ℝ => ((Real.Gamma (y / 2 + 1) : ℝ) : ℂ) := by
    funext y
    rw [← Gamma_ofReal]
    push_cast
    rfl
  have hr : DifferentiableAt ℝ (fun y : ℝ => Real.Gamma (y / 2 + 1)) x := by
    refine (Real.differentiableAt_Gamma fun m h => ?_).comp x (by fun_prop)
    have : (0 : ℝ) < x / 2 + 1 := by linarith
    rw [h] at this
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have h1' : HasDerivAt (fun y : ℝ => ((Real.Gamma (y / 2 + 1) : ℝ) : ℂ))
      (deriv (fun s : ℂ => Gamma (s / 2 + 1)) x) x := by
    rw [← hfun]; exact h1
  rw [logDeriv_apply, h1'.unique hr.hasDerivAt.ofReal_comp]
  have hG : Gamma ((x : ℂ) / 2 + 1) = ((Real.Gamma (x / 2 + 1) : ℝ) : ℂ) := congrFun hfun x
  simp only [hG]
  rw [← ofReal_div, ofReal_im]

private lemma stirling_main_im_bound {w : ℂ} {T : ℝ} (hT : 2 ≤ T) (hre : w.re = 5 / 4)
    (him : w.im = T / 2) :
    |((w - 1 / 2) * log w - w + 1 / 2 * log (2 * Real.pi)).im -
        (T / 2 * Real.log (T / 2) - T / 2 + 3 / 8 * Real.pi)| ≤ 6 / T := by
  have hlog2pi : (log (2 * Real.pi)).im = 0 := by
    rw [log_im, show (2 : ℂ) * Real.pi = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
      arg_ofReal_of_nonneg (by positivity)]
  have hw0 : w ≠ 0 := by
    intro h; rw [h] at hre; norm_num at hre
  have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw0
  have hnorm : ‖w‖ ^ 2 = 25 / 16 + T ^ 2 / 4 := by
    rw [Complex.sq_norm, normSq_apply, hre, him]; ring
  have hT2 : T / 2 ≤ ‖w‖ := by
    have := abs_im_le_norm w
    rwa [him, abs_of_pos (by linarith)] at this
  have him_eq : ((w - 1 / 2) * log w - w + 1 / 2 * log (2 * Real.pi)).im =
      3 / 4 * arg w + T / 2 * Real.log ‖w‖ - T / 2 := by
    rw [log_im] at hlog2pi
    simp only [one_div, add_im, sub_im, mul_im, sub_re, hre, inv_re, re_ofNat, normSq_ofNat,
      div_self_mul_self', log_im, him, inv_im, im_ofNat, neg_zero, zero_div, sub_zero, log_re,
      Complex.norm_mul, norm_ofNat, norm_real, Real.norm_eq_abs, Real.abs_pi, zero_mul, add_zero]
    rw [hlog2pi]
    ring
  have harg0 : 0 ≤ arg w := arg_nonneg_iff.2 (by rw [him]; linarith)
  have harg1 : arg w ≤ Real.pi / 2 :=
    (abs_le.1 (abs_arg_le_pi_div_two_iff.2 (by rw [hre]; norm_num))).2
  have hcos : Real.cos (arg w) = 5 / 4 / ‖w‖ := by rw [cos_arg hw0, hre]
  set θ := Real.pi / 2 - arg w with hθdef
  have hsin : Real.sin θ = 5 / 4 / ‖w‖ := by rw [hθdef, Real.sin_pi_div_two_sub, hcos]
  have hθ := Real.mul_le_sin (by linarith : 0 ≤ θ) (by linarith : θ ≤ Real.pi / 2)
  have hpi := Real.pi_pos
  have hpi4 := Real.pi_le_four
  have hθb : θ ≤ 5 / T := by
    have hTpos : 0 < T := by linarith
    calc θ = Real.pi / 2 * (2 / Real.pi * θ) := by field_simp
      _ ≤ Real.pi / 2 * (5 / 4 / ‖w‖) := by rw [← hsin]; gcongr
      _ ≤ Real.pi / 2 * (5 / 4 / (T / 2)) := by gcongr
      _ = 5 * Real.pi / (4 * T) := by field_simp
      _ ≤ 5 * 4 / (4 * T) := by gcongr
      _ = 5 / T := by field_simp
  have hlog1 : Real.log (T / 2) ≤ Real.log ‖w‖ := Real.log_le_log (by positivity) hT2
  have hlog2 : Real.log ‖w‖ - Real.log (T / 2) ≤ ‖w‖ / (T / 2) - 1 := by
    rw [← Real.log_div hwpos.ne' (by positivity)]
    exact Real.log_le_sub_one_of_pos (by positivity)
  have hprod : T / 2 * (Real.log ‖w‖ - Real.log (T / 2)) ≤ ‖w‖ - T / 2 := by
    calc T / 2 * (Real.log ‖w‖ - Real.log (T / 2)) ≤ T / 2 * (‖w‖ / (T / 2) - 1) := by
          gcongr
      _ = ‖w‖ - T / 2 := by field_simp
  have hdiff : ‖w‖ - T / 2 ≤ 25 / 16 / T := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  have hprod0 : 0 ≤ T / 2 * (Real.log ‖w‖ - Real.log (T / 2)) :=
    mul_nonneg (by linarith) (by linarith)
  have h6 : 5 / T * (3 / 4) + 25 / 16 / T ≤ 6 / T := by
    rw [div_mul_eq_mul_div, ← add_div, div_le_div_iff_of_pos_right (by linarith)]
    norm_num
  rw [him_eq, abs_le]
  constructor <;> nlinarith

/-- The variation of the argument of `Γ(s/2 + 1)` along `2 → 2 + iT → 1/2 + iT` is
`(T/2) log (T/2) - T/2 + 3π/8 + O(1/T)` as `T → ∞`. -/
theorem argVariationToCriticalLine_Gamma_sub_isBigO :
    (fun T : ℝ => argVariationToCriticalLine (fun s : ℂ => Gamma (s / 2 + 1)) T -
        (T / 2 * Real.log (T / 2) - T / 2 + 3 / 8 * Real.pi))
      =O[atTop] (fun T : ℝ => 1 / T) := by
  set G : ℂ → ℂ := fun s => Gamma (s / 2 + 1) with hGdef
  set U : Set ℂ := {s : ℂ | 0 < s.re} with hUdef
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_re
  have hGd : DifferentiableOn ℂ G U := fun s hs =>
    (differentiableAt_Gamma_half_add_one
      (by have : 0 < s.re := hs; linarith)).differentiableWithinAt
  have hG0 : ∀ s ∈ U, G s ≠ 0 := fun s hs =>
    Gamma_ne_zero_of_re_pos (by have : 0 < s.re := hs; simp; linarith)
  have hψ : ContinuousOn (logDeriv G) U :=
    ((hGd.analyticOnNhd hUo).deriv.continuousOn.div hGd.continuousOn hG0 :
      ContinuousOn (fun z => deriv G z / G z) U)
  -- the two legs
  set V : ℝ → ℂ := fun T => ∫ y in (0 : ℝ)..T, logDeriv G (2 + y * I) * I with hVdef
  set H : ℝ → ℂ := fun T => ∫ x in (2 : ℝ)..(1 / 2), logDeriv G (x + T * I) with hHdef
  set w : ℝ → ℂ := fun T => 5 / 4 + (T : ℂ) / 2 * I with hwdef
  have hwre : ∀ T, (w T).re = 5 / 4 := fun T => by simp [hwdef]
  have hwim : ∀ T, (w T).im = T / 2 := fun T => by simp [hwdef]
  have hvert : ∀ T : ℝ, 0 ≤ T → G (2 + T * I) = G 2 * exp (V T) := by
    intro T hT
    have := DifferentiableOn.apply_eq_mul_exp_integral_logDeriv hUo hGd hG0
      (p := fun y : ℝ => 2 + y * I) (d := I)
      (fun t => by simpa using ((hasDerivAt_id t).ofReal_comp.mul_const I).const_add 2)
      hT (fun t _ => by simp [hUdef])
    simpa only [ofReal_zero, zero_mul, add_zero] using this
  have hhor : ∀ T : ℝ, G (1 / 2 + T * I) = G (2 + T * I) * exp (H T) := by
    intro T
    have := DifferentiableOn.apply_eq_mul_exp_integral_logDeriv hUo hGd hG0
      (p := fun x : ℝ => x + T * I) (d := 1)
      (fun t => by simpa using (hasDerivAt_id t).ofReal_comp.add_const ((T : ℂ) * I))
      (by norm_num : (1 / 2 : ℝ) ≤ 2) (fun t ht => by simp [hUdef]; linarith [ht.1])
    simp only [mul_one] at this
    push_cast at this
    rw [hHdef]
    simp only
    rw [intervalIntegral.integral_symm, exp_neg, this, mul_assoc,
      mul_inv_cancel₀ (exp_ne_zero _), mul_one]
  have hG2 : G 2 = 1 := by
    simp only [hGdef]
    norm_num
  have hP : ∀ T : ℝ, 0 ≤ T → exp (V T + H T) = Gamma (w T) := by
    intro T hT
    rw [exp_add]
    have h1 := hhor T
    rw [hvert T hT, hG2, one_mul] at h1
    rw [← h1]
    simp only [hGdef, hwdef]
    congr 1
    ring
  -- continuity of the two legs in `T`
  have hVc : Continuous V := by
    have hg : Continuous (fun y : ℝ => logDeriv G (2 + y * I) * I) :=
      (hψ.comp_continuous (by fun_prop) (fun y => by simp [hUdef])).mul continuous_const
    exact intervalIntegral.continuous_primitive (fun a b => hg.intervalIntegrable a b) 0
  have hHc : Continuous H := by
    have hcl : H = fun T : ℝ => ∫ x in (2 : ℝ)..(1 / 2),
        logDeriv G (((max (1 / 2) (min x 2) : ℝ) : ℂ) + T * I) := by
      funext T
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_ge (by norm_num)] at hx
      simp only
      rw [min_eq_left hx.2, max_eq_right hx.1]
    rw [hcl]
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    have hq : Continuous
        (fun q : ℝ × ℝ => ((max (1 / 2) (min q.2 2) : ℝ) : ℂ) + (q.1 : ℂ) * I) := by
      fun_prop
    exact hψ.comp_continuous hq (fun q => by simp [hUdef])
  -- Stirling at `w T + N`
  obtain ⟨C, hC⟩ := Complex.Gamma_eq_exp_stirling_sector (Real.pi / 2) (by positivity)
  set N : ℕ := ⌈4 * |C|⌉₊ + 1 with hN
  have hNC : 4 * |C| ≤ N := by
    rw [hN]; push_cast
    linarith [Nat.le_ceil (4 * |C|)]
  have hN1 : (1 : ℝ) ≤ N := by
    rw [hN]; push_cast
    linarith [Nat.cast_nonneg (α := ℝ) ⌈4 * |C|⌉₊]
  set S : ℂ → ℂ := fun z => (z - 1 / 2) * log z - z + 1 / 2 * log (2 * Real.pi) with hSdef
  have hwNre : ∀ T : ℝ, ∀ j : ℕ, (w T + j).re = 5 / 4 + j := fun T j => by simp [hwre]
  have hwNpos : ∀ T : ℝ, ∀ j : ℕ, 0 < (w T + j).re := fun T j => by
    rw [hwNre]; positivity
  have hwN0 : ∀ T : ℝ, ∀ j : ℕ, w T + j ≠ 0 := fun T j h => by
    have := hwNpos T j; rw [h] at this; simp at this
  have hstir : ∀ T : ℝ, ∃ E : ℂ, ‖E‖ ≤ |C| / ‖w T + N‖ ∧
      Gamma (w T + N) = exp (S (w T + N) + E) := by
    intro T
    have harg := abs_arg_le_pi_div_two_iff.2 (hwNpos T N).le
    obtain ⟨E, hE, hΓ⟩ := hC (w T + N) (hwN0 T N) (by linarith [(abs_le.1 harg).1])
      (by linarith [(abs_le.1 harg).2])
    refine ⟨E, hE.trans ?_, hΓ⟩
    gcongr
    exact le_abs_self C
  choose E hE hEΓ using hstir
  have hEsmall : ∀ T, ‖E T‖ ≤ 1 / 4 := by
    intro T
    refine (hE T).trans ?_
    have h1 : (N : ℝ) ≤ ‖w T + N‖ := by
      have := abs_re_le_norm (w T + N)
      rw [hwNre, abs_of_pos (by positivity)] at this
      linarith
    rw [div_le_iff₀ (by linarith)]
    nlinarith [abs_nonneg C]
  -- the Gamma shift
  have hshift : ∀ z : ℂ, 0 < z.re → ∀ n : ℕ,
      Gamma (z + n) = Gamma z * ∏ j ∈ Finset.range n, (z + j) := by
    intro z hz n
    induction n with
    | zero => simp
    | succ n ih =>
      have hne : z + n ≠ 0 := by
        intro h
        have : (z + n).re = 0 := by rw [h]; simp
        simp at this
        linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      rw [Finset.prod_range_succ, Nat.cast_succ, ← add_assoc, Gamma_add_one _ hne, ih]
      ring
  set Q : ℝ → ℂ := fun T => S (w T + N) - ∑ j ∈ Finset.range N, log (w T + j) with hQdef
  set D : ℝ → ℂ := fun T => V T + H T - Q T with hDdef
  have hDE : ∀ T : ℝ, 0 ≤ T → ∃ m : ℤ, D T - E T = m * (2 * Real.pi * I) := by
    intro T hT
    rw [← exp_eq_one_iff]
    have h1 : exp (∑ j ∈ Finset.range N, log (w T + j)) = ∏ j ∈ Finset.range N, (w T + j) := by
      rw [exp_sum]
      exact Finset.prod_congr rfl fun j _ => exp_log (hwN0 T j)
    have h2 : D T - E T = (V T + H T + ∑ j ∈ Finset.range N, log (w T + j)) -
        (S (w T + N) + E T) := by
      simp only [hDdef, hQdef]; ring
    have hwpos : 0 < (w T).re := by rw [hwre]; norm_num
    rw [h2, exp_sub, exp_add, hP T hT, h1, ← hEΓ T, ← hshift _ hwpos N,
      div_self (Gamma_ne_zero_of_re_pos (by simpa using hwNpos T N))]
  have hDc : Continuous D := by
    have hlogc : ∀ j : ℕ, Continuous (fun T : ℝ => log (w T + j)) := fun j =>
      continuous_iff_continuousAt.2 fun T =>
        ContinuousAt.clog (by fun_prop) (mem_slitPlane_iff.2 (Or.inl (hwNpos T j)))
    have hSc : Continuous (fun T : ℝ => S (w T + N)) := by
      simp only [hSdef]
      exact (((by fun_prop : Continuous fun T : ℝ => w T + N - 1 / 2)).mul (hlogc N)).sub
        (by fun_prop) |>.add continuous_const
    exact (hVc.add hHc).sub (hSc.sub (continuous_finsetSum _ fun j _ => hlogc j))
  -- at `T = 0` everything is real
  have hlogim : ∀ r : ℝ, 0 ≤ r → (log r).im = 0 := fun r hr => by
    rw [log_im, arg_ofReal_of_nonneg hr]
  have hlog2pi : (log (2 * Real.pi)).im = 0 := by
    rw [show (2 : ℂ) * Real.pi = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl]
    exact hlogim _ (by positivity)
  have hH0 : (H 0).im = 0 := by
    have : H 0 = ∫ x in (2 : ℝ)..(1 / 2), (((logDeriv G x).re : ℝ) : ℂ) := by
      simp only [hHdef]
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_ge (by norm_num)] at hx
      simp only [ofReal_zero, zero_mul, add_zero]
      refine Complex.ext (by simp) ?_
      rw [ofReal_im]
      exact im_logDeriv_Gamma_half_add_one (by linarith [hx.1])
    rw [this, intervalIntegral.integral_ofReal, ofReal_im]
  have hwreal : ∀ j : ℕ, w 0 + j = ((5 / 4 + j : ℝ) : ℂ) := by
    intro j; rw [hwdef]; push_cast; ring
  have hQ0 : (Q 0).im = 0 := by
    have hS : ∀ r : ℝ, 0 ≤ r → (S r).im = 0 := by
      intro r hr
      simp only [hSdef]
      simp [mul_im, hlogim r hr, hlog2pi]
    simp only [hQdef, sub_im, im_sum, hwreal]
    rw [hS _ (by positivity), Finset.sum_eq_zero (fun j _ => hlogim _ (by positivity))]
    simp
  have hD0 : (D 0).im = 0 := by
    simp only [hDdef, sub_im, add_im, hQ0, hH0, hVdef, intervalIntegral.integral_same,
      zero_im]
    norm_num
  have hrel : ∀ t : ℝ, 0 ≤ t → ∃ m : ℤ, (D t).im - 2 * Real.pi * m = (E t).im := by
    intro t ht
    obtain ⟨m, hm⟩ := hDE t ht
    refine ⟨m, ?_⟩
    have := congrArg im hm
    simp at this
    linarith
  have hDim : ∀ T : ℝ, 0 ≤ T → (D T).im = (E T).im := by
    intro T hT
    have hEi : ∀ t, |(E t).im| ≤ 1 / 4 := fun t => (abs_im_le_norm _).trans (hEsmall t)
    have key := abs_le_half_of_near_lattice (f := fun t => (D t).im) (a := 0) (b := T)
      (continuous_im.comp hDc).continuousOn (by simp [hD0])
      (fun t ht => by
        obtain ⟨m, hm⟩ := hrel t ht.1
        exact ⟨m, by rw [hm]; linarith [hEi t]⟩) T ⟨hT, le_rfl⟩
    obtain ⟨m, hm⟩ := hrel T hT
    have hm0 : m = 0 := int_eq_zero_of_abs_sub_le (x := (D T).im) (by rw [hm]; linarith [hEi T])
      (by linarith [abs_le.1 key])
    subst hm0
    simpa using hm
  -- the estimate
  refine IsBigO.of_bound (2 * |C| + 4 * N + 6) (eventually_atTop.2 ⟨2, fun T hT => ?_⟩)
  have hTpos : 0 < T := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / T)]
  have harg : argVariationToCriticalLine G T = (V T + H T).im := by
    rw [add_im]; rfl
  have hVH : V T + H T = D T + Q T := by simp only [hDdef]; ring
  have hwT : ∀ j : ℕ, T / 2 ≤ ‖w T + j‖ := by
    intro j
    have := abs_im_le_norm (w T + j)
    simp only [add_im, natCast_im, add_zero, hwim] at this
    rwa [abs_of_pos (by positivity)] at this
  have htel : Q T = S (w T) + ∑ j ∈ Finset.range N,
      (S (w T + j + 1) - S (w T + j) - log (w T + j)) := by
    rw [Finset.sum_sub_distrib]
    have := Finset.sum_range_sub (fun j : ℕ => S (w T + j)) N
    simp only [Nat.cast_succ, ← add_assoc, Nat.cast_zero, add_zero] at this
    rw [this]
    simp only [hQdef]
    ring
  have hY : ∀ j : ℕ, ‖S (w T + j + 1) - S (w T + j) - log (w T + j)‖ ≤ 4 / T := by
    intro j
    have h1 : 1 ≤ ‖w T + j‖ := le_trans (by linarith) (hwT j)
    refine (norm_stirling_step (hwNpos T j) h1).trans ?_
    rw [div_le_div_iff₀ (by linarith) hTpos]
    nlinarith [hwT j]
  have hsum : |(∑ j ∈ Finset.range N,
      (S (w T + j + 1) - S (w T + j) - log (w T + j))).im| ≤ N * (4 / T) := by
    rw [im_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun j _ => (abs_im_le_norm _).trans (hY j)).trans ?_
    simp
  have hEb : |(E T).im| ≤ 2 * |C| / T := by
    refine (abs_im_le_norm _).trans ((hE T).trans ?_)
    rw [div_le_div_iff₀ (by linarith [hwT N]) hTpos]
    nlinarith [hwT N, abs_nonneg C]
  have hmain := stirling_main_im_bound (w := w T) hT (hwre T) (hwim T)
  rw [harg, hVH, htel, add_im, hDim T hTpos.le, add_im]
  have hfinal : 2 * |C| / T + N * (4 / T) + 6 / T = (2 * |C| + 4 * N + 6) * (1 / T) := by
    field_simp
  rw [← hfinal]
  have := abs_add_three ((E T).im) ((∑ j ∈ Finset.range N,
      (S (w T + j + 1) - S (w T + j) - log (w T + j))).im)
    ((S (w T)).im - (T / 2 * Real.log (T / 2) - T / 2 + 3 / 8 * Real.pi))
  calc _ = |(E T).im + (∑ j ∈ Finset.range N,
      (S (w T + j + 1) - S (w T + j) - log (w T + j))).im +
        ((S (w T)).im - (T / 2 * Real.log (T / 2) - T / 2 + 3 / 8 * Real.pi))| := by
        ring_nf
    _ ≤ _ := this.trans (add_le_add (add_le_add hEb hsum) hmain)
