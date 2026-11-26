/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.PSeriesComplex
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.ZetaValues

/-!
# The reciprocal zeta bound under the Riemann hypothesis

For each fixed `1 / 2 < σ ≤ 1` and `ε > 0`, the reciprocal of `ζ(σ + it)` is bounded by
`C * |t| ^ ε` for sufficiently large `|t|`, assuming the Riemann hypothesis.
The private helpers construct and bound a holomorphic logarithm of `ζ`.

Source: Kampamolla Venkatasubbareddy and Ayyadurai Sankaranarayanan, *On the
Distribution of the Restricted Sequence of Integers 2^{ω(n)}*, INTEGERS 24
(2024), Article A110, Lemma 8 (`integers-2024-A110-lem-8`).
-/

open Complex

namespace MetaMathlibExt

section PolynomialBound

open MeasureTheory Filter Topology Asymptotics

/-- The integral `∫_1^∞ {x} x^{-s-1} dx`. -/
private noncomputable def fractIntegral (s : ℂ) : ℂ :=
  ∫ x in Set.Ioi (1 : ℝ), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1))

/-- The integrand `{x} x^{-s-1}` is bounded by `x^{-re s - 1}` for `x > 0`. -/
private theorem norm_fract_mul_le {s : ℂ} {x : ℝ} (hx : 0 < x) :
    ‖((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1))‖ ≤ x ^ (-(s.re + 1)) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Int.fract_nonneg x)]
  have h1 : (-(s + 1)).re = -(s.re + 1) := by simp
  rw [h1]
  calc Int.fract x * x ^ (-(s.re + 1)) ≤ 1 * x ^ (-(s.re + 1)) := by
        gcongr
        exact (Int.fract_lt_one x).le
    _ = x ^ (-(s.re + 1)) := one_mul _

/-- The integrand `{x} x^{-s-1}` is measurable. -/
private theorem measurable_fract_mul (s : ℂ) :
    Measurable (fun x : ℝ => ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1))) :=
  (Complex.measurable_ofReal.comp measurable_fract).mul
    (Complex.measurable_ofReal.pow_const _)

/-- The integrand `{x} x^{-s-1}` is integrable on `(1, ∞)` for `re s > 0`. -/
private theorem integrableOn_fract {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1))) (Set.Ioi 1) := by
  have hg : IntegrableOn (fun x : ℝ => x ^ (-(s.re + 1))) (Set.Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  refine hg.mono' (measurable_fract_mul s).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  exact Eventually.of_forall fun x hx => norm_fract_mul_le (lt_trans one_pos hx)

/-- `‖∫_1^∞ {x} x^{-s-1} dx‖ ≤ 1 / re s` for `re s > 0`. -/
private theorem norm_fractIntegral_le {s : ℂ} (hs : 0 < s.re) :
    ‖fractIntegral s‖ ≤ 1 / s.re := by
  have hint : ∫ x in Set.Ioi (1 : ℝ), x ^ (-(s.re + 1)) = 1 / s.re := by
    rw [integral_Ioi_rpow_of_lt (by linarith) one_pos, Real.one_rpow]
    have : -(s.re + 1) + 1 = -s.re := by ring
    rw [this, div_neg, neg_div, neg_neg]
  rw [← hint]
  refine norm_integral_le_of_norm_le (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos) ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  exact Eventually.of_forall fun x hx => norm_fract_mul_le (lt_trans one_pos hx)

/-- For `1 < re s`, `ζ₀(s) = 1 - s ∫_1^∞ {x} x^{-s-1} dx`. -/
private theorem riemannZeta₀_eq_of_one_lt {s : ℂ} (hs : 1 < s.re) :
    riemannZeta₀ s = 1 - s * fractIntegral s := by
  have hs0 : 0 < s.re := lt_trans one_pos hs
  have hs1 : s ≠ 1 := by
    rintro rfl
    simp at hs
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (1 : ℕ → ℂ) k) =O[atTop]
      fun n : ℕ => ((n : ℝ) ^ (1 : ℝ) : ℝ) := by
    refine IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
    simp [Real.rpow_one]
  have hL := LSeries_eq_mul_integral (1 : ℕ → ℂ) zero_le_one (by simpa using hs)
    (LSeriesSummable_one_iff.mpr hs) hO
  rw [LSeries_one_eq_riemannZeta hs] at hL
  have hcongr : ∫ t in Set.Ioi (1 : ℝ),
      (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℕ → ℂ) k) * (t : ℂ) ^ (-(s + 1)) =
      ∫ t in Set.Ioi (1 : ℝ), ((t : ℂ) ^ (-s) -
        ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) < t := lt_trans one_pos ht
    have hsum : (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℕ → ℂ) k) = ((t - Int.fract t : ℝ) : ℂ) := by
      simp only [Pi.one_apply, Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right,
        nsmul_eq_mul, mul_one]
      rw [← Int.self_sub_floor, sub_sub_cancel, ← natCast_floor_eq_intCast_floor ht0.le]
      simp
    have hpow : (t : ℂ) ^ (-s) = (t : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
      have hne : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
      rw [show -s = (1 : ℂ) + (-(s + 1)) by ring, Complex.cpow_add _ _ hne, Complex.cpow_one]
    rw [hsum, hpow, Complex.ofReal_sub]
    ring
  rw [hcongr, integral_sub (integrableOn_Ioi_cpow_of_lt (by simp; linarith) one_pos)
    (integrableOn_fract hs0), integral_Ioi_cpow_of_lt (by simp; linarith) one_pos] at hL
  rw [Complex.ofReal_one, Complex.one_cpow] at hL
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hsub' : -s + 1 ≠ 0 := by
    intro h
    apply hsub
    linear_combination -h
  have hz := riemannZeta_eq_inv_sub_add hs1
  rw [hz] at hL
  unfold fractIntegral
  have : riemannZeta₀ s = s * (-1 / (-s + 1) -
      ∫ x in Set.Ioi (1 : ℝ), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1))) - (s - 1)⁻¹ := by
    rw [← hL]; ring
  rw [this]
  field_simp
  ring

/-- The integral as a Mellin transform. -/
private theorem fractIntegral_eq_mellin (s : ℂ) :
    fractIntegral s =
      mellin (Set.indicator (Set.Ioi (1 : ℝ)) (fun x : ℝ => ((Int.fract x : ℝ) : ℂ))) (-s) := by
  rw [mellin, fractIntegral]
  have h : ∀ t : ℝ, (t : ℂ) ^ (-s - 1) •
      Set.indicator (Set.Ioi (1 : ℝ)) (fun x : ℝ => ((Int.fract x : ℝ) : ℂ)) t =
      Set.indicator (Set.Ioi (1 : ℝ))
        (fun x : ℝ => ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1))) t := by
    intro t
    by_cases ht : t ∈ Set.Ioi (1 : ℝ)
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, smul_eq_mul, mul_comm,
        show -s - 1 = -(s + 1) by ring]
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, smul_zero]
  simp_rw [h]
  rw [setIntegral_indicator measurableSet_Ioi, Set.Ioi_inter_Ioi, max_eq_right zero_le_one]

/-- `s ↦ ∫_1^∞ {x} x^{-s-1} dx` is complex differentiable on `re s > 0`. -/
private theorem differentiableAt_fractIntegral {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ fractIntegral s := by
  set F : ℝ → ℂ := Set.indicator (Set.Ioi (1 : ℝ)) (fun x : ℝ => ((Int.fract x : ℝ) : ℂ)) with hF
  have hFle : ∀ x, ‖F x‖ ≤ 1 := by
    intro x
    by_cases hx : x ∈ Set.Ioi (1 : ℝ)
    · rw [hF, Set.indicator_of_mem hx, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Int.fract_nonneg x)]
      exact (Int.fract_lt_one x).le
    · rw [hF, Set.indicator_of_notMem hx, norm_zero]
      exact zero_le_one
  have hFmeas : Measurable F :=
    (Complex.measurable_ofReal.comp measurable_fract).indicator measurableSet_Ioi
  have hloc : LocallyIntegrableOn F (Set.Ioi (0 : ℝ)) := by
    rw [locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed]
    intro k _ hk
    exact Measure.integrableOn_of_bounded hk.measure_lt_top.ne hFmeas.aestronglyMeasurable
      (M := 1) (Eventually.of_forall fun x => hFle x)
  have htop : F =O[atTop] fun x : ℝ => x ^ (-(0 : ℝ)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [neg_zero, Real.rpow_zero, norm_one, one_mul]
    exact hFle x
  have hbot : F =O[𝓝[>] (0 : ℝ)] fun x : ℝ => x ^ (-((-s).re - 1)) := by
    refine EventuallyEq.trans_isBigO ?_ (isBigO_zero _ _)
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht
    rw [hF, Set.indicator_of_notMem (by simpa using ht.2.le)]
  have hd : DifferentiableAt ℂ (mellin F) (-s) :=
    mellin_differentiableAt_of_isBigO_rpow hloc htop (by simpa using hs) hbot
      (sub_lt_self _ one_pos)
  have hfun : fractIntegral = fun s => mellin F (-s) := by
    funext s
    exact fractIntegral_eq_mellin s
  rw [hfun]
  exact hd.comp s (by fun_prop)

/-- For `0 < re s`, `ζ₀(s) = 1 - s ∫_1^∞ {x} x^{-s-1} dx`. -/
private theorem riemannZeta₀_eq {s : ℂ} (hs : 0 < s.re) :
    riemannZeta₀ s = 1 - s * fractIntegral s := by
  set U : Set ℂ := {s : ℂ | 0 < s.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have h1 : AnalyticOnNhd ℂ riemannZeta₀ U :=
    (differentiable_riemannZeta₀.differentiableOn).analyticOnNhd hUo
  have h2 : AnalyticOnNhd ℂ (fun s => 1 - s * fractIntegral s) U := by
    refine DifferentiableOn.analyticOnNhd ?_ hUo
    intro z hz
    exact ((differentiableAt_const _).sub
      (differentiableAt_id.mul (differentiableAt_fractIntegral hz))).differentiableWithinAt
  have hpre : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have h2U : (2 : ℂ) ∈ U := by simp [hU]
  have hev : riemannZeta₀ =ᶠ[𝓝 (2 : ℂ)] fun s => 1 - s * fractIntegral s := by
    have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (show (1 : ℝ) < (2 : ℂ).re by simp)] with z hz
    exact riemannZeta₀_eq_of_one_lt hz
  exact h1.eqOn_of_preconnected_of_eventuallyEq h2 hpre h2U hev hs

/-- Polynomial bound for `ζ` on the half-plane `re s > 0`:
`‖ζ(s)‖ ≤ 1 / ‖s - 1‖ + 1 + ‖s‖ / re s`. -/
private theorem norm_riemannZeta_le {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ‖riemannZeta s‖ ≤ 1 / ‖s - 1‖ + 1 + ‖s‖ / s.re := by
  rw [riemannZeta_eq_inv_sub_add hs1, riemannZeta₀_eq hs]
  calc ‖(s - 1)⁻¹ + (1 - s * fractIntegral s)‖
      ≤ ‖(s - 1)⁻¹‖ + (‖(1 : ℂ)‖ + ‖s * fractIntegral s‖) :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_sub_le _ _))
    _ ≤ 1 / ‖s - 1‖ + (1 + ‖s‖ * (1 / s.re)) := by
        rw [norm_inv, norm_one, norm_mul, one_div]
        gcongr
        exact norm_fractIntegral_le hs
    _ = 1 / ‖s - 1‖ + 1 + ‖s‖ / s.re := by ring

end PolynomialBound

section HolomorphicLogarithm

/-- A nonvanishing holomorphic function on a disc has a holomorphic logarithm there: a
primitive `g` of `f' / f` with `g c = log (f c)` and `exp ∘ g = f`. -/
private theorem exists_log {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball c R)) (hf0 : ∀ z ∈ Metric.ball c R, f z ≠ 0) :
    ∃ g : ℂ → ℂ, (∀ z ∈ Metric.ball c R, HasDerivAt g (deriv f z / f z) z) ∧
      g c = Complex.log (f c) ∧ ∀ z ∈ Metric.ball c R, Complex.exp (g z) = f z := by
  have hopen : IsOpen (Metric.ball c R) := Metric.isOpen_ball
  have han : AnalyticOnNhd ℂ f (Metric.ball c R) := hf.analyticOnNhd hopen
  have hderiv : DifferentiableOn ℂ (deriv f) (Metric.ball c R) := han.deriv.differentiableOn
  have hq : DifferentiableOn ℂ (fun z => deriv f z / f z) (Metric.ball c R) :=
    hderiv.div hf hf0
  obtain ⟨g, hgc, hg⟩ := (hq.isExactOn_ball).with_val_at c (Complex.log (f c))
  refine ⟨g, hg, hgc, ?_⟩
  have hφ : ∀ z ∈ Metric.ball c R,
      HasDerivAt (fun z => f z * Complex.exp (-g z)) 0 z := by
    intro z hz
    have hfz : HasDerivAt f (deriv f z) z :=
      (hf.differentiableAt (hopen.mem_nhds hz)).hasDerivAt
    have h2 : HasDerivAt (fun z => Complex.exp (-g z))
        (Complex.exp (-g z) * (-(deriv f z / f z))) z :=
      ((hg z hz).neg).cexp
    convert hfz.mul h2 using 1
    field_simp [hf0 z hz]
    ring
  intro z hz
  have hc : c ∈ Metric.ball c R :=
    Metric.mem_ball_self (lt_of_le_of_lt dist_nonneg (Metric.mem_ball.mp hz))
  have hconst : f z * Complex.exp (-g z) = f c * Complex.exp (-g c) :=
    hopen.is_const_of_deriv_eq_zero (convex_ball c R).isPreconnected
      (fun w hw => (hφ w hw).differentiableAt.differentiableWithinAt)
      (fun w hw => (hφ w hw).deriv) hz hc
  have h1 : f c * Complex.exp (-g c) = 1 := by
    rw [hgc, Complex.exp_neg, Complex.exp_log (hf0 c hc)]
    exact mul_inv_cancel₀ (hf0 c hc)
  rw [h1, Complex.exp_neg] at hconst
  have hne : Complex.exp (g z) ≠ 0 := Complex.exp_ne_zero _
  field_simp at hconst
  exact hconst.symm

/-- On a disc where `f` takes values in the slit plane, a primitive of `f' / f` that agrees
with `log ∘ f` at the centre is `log ∘ f`. -/
private theorem eq_log_of_slitPlane {f g : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball c r))
    (hslit : ∀ z ∈ Metric.ball c r, f z ∈ Complex.slitPlane)
    (hg : ∀ z ∈ Metric.ball c r, HasDerivAt g (deriv f z / f z) z)
    (hgc : g c = Complex.log (f c)) :
    ∀ z ∈ Metric.ball c r, g z = Complex.log (f z) := by
  intro z hz
  have hopen : IsOpen (Metric.ball c r) := Metric.isOpen_ball
  have hc : c ∈ Metric.ball c r :=
    Metric.mem_ball_self (lt_of_le_of_lt dist_nonneg (Metric.mem_ball.mp hz))
  have hψ : ∀ w ∈ Metric.ball c r,
      HasDerivAt (fun w => g w - Complex.log (f w)) 0 w := by
    intro w hw
    have hfw : HasDerivAt f (deriv f w) w :=
      (hf.differentiableAt (hopen.mem_nhds hw)).hasDerivAt
    have := (hg w hw).fun_sub (hfw.clog (hslit w hw))
    simpa using this
  have hconst := hopen.is_const_of_deriv_eq_zero (convex_ball c r).isPreconnected
    (fun w hw => (hψ w hw).differentiableAt.differentiableWithinAt)
    (fun w hw => (hψ w hw).deriv) hz hc
  rw [hgc, sub_self] at hconst
  exact sub_eq_zero.mp hconst

/-- **Hadamard's three-circles theorem**, from the three-lines theorem applied to
`w ↦ g (c + exp w)` on the strip `log r₁ ≤ re w ≤ log r₃`. -/
private theorem three_circles {g : ℂ → ℂ} {c : ℂ} {r₁ r₃ R M₁ M₃ : ℝ}
    (hr₁ : 0 < r₁) (h13 : r₁ < r₃) (h3R : r₃ < R)
    (hg : DifferentiableOn ℂ g (Metric.ball c R))
    (hM₁ : ∀ z, ‖z - c‖ = r₁ → ‖g z‖ ≤ M₁) (hM₃ : ∀ z, ‖z - c‖ = r₃ → ‖g z‖ ≤ M₃)
    {z : ℂ} (hz₁ : r₁ ≤ ‖z - c‖) (hz₃ : ‖z - c‖ ≤ r₃) :
    ‖g z‖ ≤ M₁ ^ (1 - (Real.log ‖z - c‖ - Real.log r₁) / (Real.log r₃ - Real.log r₁)) *
      M₃ ^ ((Real.log ‖z - c‖ - Real.log r₁) / (Real.log r₃ - Real.log r₁)) := by
  have hr₃ : 0 < r₃ := hr₁.trans h13
  have hlu : Real.log r₁ < Real.log r₃ := Real.log_lt_log hr₁ h13
  set F : ℂ → ℂ := fun w => g (c + Complex.exp w) with hF
  have hnorm : ∀ w : ℂ, ‖c + Complex.exp w - c‖ = Real.exp w.re := by
    intro w; simp [Complex.norm_exp]
  have hmem : ∀ w : ℂ, w.re ≤ Real.log r₃ → c + Complex.exp w ∈ Metric.closedBall c r₃ := by
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm, hnorm]
    calc Real.exp w.re ≤ Real.exp (Real.log r₃) := Real.exp_le_exp.mpr hw
      _ = r₃ := Real.exp_log hr₃
  have hball : Metric.closedBall c r₃ ⊆ Metric.ball c R := Metric.closedBall_subset_ball h3R
  have hFdiff : DifferentiableOn ℂ F
      (HadamardThreeLines.verticalClosedStrip (Real.log r₁) (Real.log r₃)) := by
    intro w hw
    have hwu : w.re ≤ Real.log r₃ := hw.2
    have hgd : DifferentiableAt ℂ g (c + Complex.exp w) :=
      hg.differentiableAt (Metric.isOpen_ball.mem_nhds (hball (hmem w hwu)))
    have hin : DifferentiableAt ℂ (fun w => c + Complex.exp w) w :=
      (differentiableAt_const c).add Complex.differentiable_exp.differentiableAt
    exact (hgd.comp w hin).differentiableWithinAt
  have hd : DiffContOnCl ℂ F (HadamardThreeLines.verticalStrip (Real.log r₁) (Real.log r₃)) := by
    apply DifferentiableOn.diffContOnCl
    have : closure (HadamardThreeLines.verticalStrip (Real.log r₁) (Real.log r₃)) =
        HadamardThreeLines.verticalClosedStrip (Real.log r₁) (Real.log r₃) := by
      simp only [HadamardThreeLines.verticalStrip, HadamardThreeLines.verticalClosedStrip,
        closure_preimage_re, closure_Ioo hlu.ne]
    rw [this]; exact hFdiff
  have hgcont : ContinuousOn g (Metric.closedBall c r₃) := (hg.mono hball).continuousOn
  obtain ⟨B, hB⟩ := (isCompact_closedBall c r₃).exists_bound_of_continuousOn hgcont
  have hBdd : BddAbove ((norm ∘ F) ''
      HadamardThreeLines.verticalClosedStrip (Real.log r₁) (Real.log r₃)) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact hB _ (hmem w hw.2)
  have ha : ∀ w ∈ Complex.re ⁻¹' {Real.log r₁}, ‖F w‖ ≤ M₁ := by
    intro w hw
    apply hM₁
    rw [hnorm]
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hw
    rw [hw]; exact Real.exp_log hr₁
  have hb : ∀ w ∈ Complex.re ⁻¹' {Real.log r₃}, ‖F w‖ ≤ M₃ := by
    intro w hw
    apply hM₃
    rw [hnorm]
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hw
    rw [hw]; exact Real.exp_log hr₃
  have hzc : z - c ≠ 0 := by
    intro h; rw [h, norm_zero] at hz₁; linarith
  have hwre : (Complex.log (z - c)).re = Real.log ‖z - c‖ := Complex.log_re _
  have hwmem : Complex.log (z - c) ∈
      HadamardThreeLines.verticalClosedStrip (Real.log r₁) (Real.log r₃) := by
    simp only [HadamardThreeLines.verticalClosedStrip, Set.mem_preimage, Set.mem_Icc, hwre]
    exact ⟨Real.log_le_log hr₁ hz₁, Real.log_le_log (by linarith) hz₃⟩
  have key :=
    HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip' hlu hwmem hd hBdd ha hb
  have hFw : F (Complex.log (z - c)) = g z := by
    simp only [hF, Complex.exp_log hzc, add_sub_cancel]
  rw [hFw, hwre] at key
  exact key

end HolomorphicLogarithm

section Lindelof

open Metric

/-- For `2 ≤ re z`, `ζ z` is within `π²/6 - 1` of `1`. -/
private theorem norm_riemannZeta_sub_one_le {z : ℂ} (hz : 2 ≤ z.re) :
    ‖riemannZeta z - 1‖ ≤ Real.pi ^ 2 / 6 - 1 := by
  have hz1 : 1 < z.re := by linarith
  have hsum : Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ z) := by
    have := (Complex.summable_one_div_nat_cpow.mpr hz1)
    exact (summable_nat_add_iff 1).mpr this |>.congr fun n => by push_cast; ring_nf
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hz1, hsum.tsum_eq_zero_add]
  simp only [CharP.cast_eq_zero, zero_add, one_cpow, div_one, add_sub_cancel_left]
  have hreal : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 2) ^ 2) (Real.pi ^ 2 / 6 - 1) := by
    have h := (hasSum_nat_add_iff' 2).mpr hasSum_zeta_two
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, CharP.cast_eq_zero,
      Nat.cast_one] at h
    norm_num at h
    convert h using 2 with n
    ring
  refine tsum_of_norm_bounded hreal fun n => ?_
  have hcast : ((n + 1 : ℕ) : ℂ) + 1 = ((n + 2 : ℕ) : ℂ) := by push_cast; ring
  rw [hcast, norm_div, norm_one, Complex.norm_natCast_cpow_of_pos (by omega)]
  have h2 : ((n + 2 : ℕ) : ℝ) ^ (2 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) ^ z.re :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n + 2)) hz
  rw [Real.rpow_two] at h2
  have h3 : ((n + 2 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
  rw [h3] at h2 ⊢
  exact one_div_le_one_div_of_le (by positivity) h2

/-- On the closed disc `‖w - 1‖ ≤ 2/3`, the principal logarithm is bounded by `6`. -/
private theorem norm_log_le_six {w : ℂ} (hw : ‖w - 1‖ ≤ 2 / 3) : ‖Complex.log w‖ ≤ 6 := by
  have hw1 : 1 / 3 ≤ ‖w‖ := by
    have := norm_sub_norm_le (1 : ℂ) (1 - w)
    rw [norm_one, sub_sub_cancel, norm_sub_rev] at this
    linarith
  have hw2 : ‖w‖ ≤ 3 := by
    have := norm_le_norm_add_norm_sub' w 1
    rw [norm_one] at this
    linarith
  have hlog3 : Real.log 3 ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have := Real.add_one_le_exp (2 : ℝ)
    linarith
  have hre : |Real.log ‖w‖| ≤ 2 := by
    rw [abs_le]
    constructor
    · have : Real.log (1 / 3) ≤ Real.log ‖w‖ := Real.log_le_log (by norm_num) hw1
      rw [one_div, Real.log_inv] at this
      linarith
    · have : Real.log ‖w‖ ≤ Real.log 3 := Real.log_le_log (by linarith) hw2
      linarith
  calc ‖Complex.log w‖ ≤ |(Complex.log w).re| + |(Complex.log w).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ = |Real.log ‖w‖| + |Complex.arg w| := by rw [Complex.log_re, Complex.log_im]
    _ ≤ 2 + 4 := add_le_add hre ((Complex.abs_arg_le_pi w).trans Real.pi_le_four)
    _ = 6 := by norm_num

/-- `π² / 6 - 1 ≤ 2 / 3`. -/
private theorem pi_sq_div_six_sub_one_le : Real.pi ^ 2 / 6 - 1 ≤ 2 / 3 := by
  have := Real.pi_lt_d2
  nlinarith [Real.pi_pos]

/-- Under RH: for `1/2 + δ ≤ σ ≤ 1` and `4 ≤ |t|`, `‖ζ(σ + it)⁻¹‖ ≤ exp (K (log |t|)^a)` with
`a < 1`. -/
private theorem norm_inv_riemannZeta_le_exp (hRH : RiemannHypothesis) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1 / 4) :
    ∃ K a : ℝ, a < 1 ∧ ∀ σ t : ℝ, 1 / 2 + δ ≤ σ → σ ≤ 1 → 4 ≤ |t| →
      ‖(riemannZeta (σ + t * I))⁻¹‖ ≤ Real.exp (K * Real.log |t| ^ a) := by
  set a : ℝ := Real.log (7 / 2 - δ) / Real.log (7 / 2 - δ / 2) with ha_def
  have hl1 : 0 < Real.log (7 / 2 - δ) := Real.log_pos (by linarith)
  have hl2 : 0 < Real.log (7 / 2 - δ / 2) := Real.log_pos (by linarith)
  have hl12 : Real.log (7 / 2 - δ) < Real.log (7 / 2 - δ / 2) :=
    Real.log_lt_log (by linarith) (by linarith)
  have ha1 : a < 1 := (div_lt_one hl2).2 hl12
  have ha0 : 0 ≤ a := div_nonneg hl1.le hl2.le
  refine ⟨6 * (252 / δ) ^ a, a, ha1, ?_⟩
  intro σ t hσ1 hσ2 ht
  have ht0 : 0 < |t| := by linarith
  have hL1 : 1 ≤ Real.log |t| := by
    rw [Real.le_log_iff_exp_le ht0]
    have := Real.exp_one_lt_d9
    linarith
  set c : ℂ := 4 + t * I with hc
  set R : ℝ := 7 / 2 - δ / 4 with hR
  set r₃ : ℝ := 7 / 2 - δ / 2 with hr₃
  have hcre : c.re = 4 := by simp [hc]
  have hcim : c.im = t := by simp [hc]
  have hgeo : ∀ z ∈ ball c R, 1 / 2 + δ / 4 < z.re ∧ 1 / 2 ≤ |z.im| ∧ ‖z‖ ≤ |t| + 8 := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    have h1 : |(z - c).re| ≤ ‖z - c‖ := Complex.abs_re_le_norm _
    have h2 : |(z - c).im| ≤ ‖z - c‖ := Complex.abs_im_le_norm _
    rw [sub_re, hcre] at h1
    rw [sub_im, hcim] at h2
    have hzc : ‖z‖ ≤ ‖c‖ + ‖z - c‖ := norm_le_norm_add_norm_sub' z c
    have hcn : ‖c‖ ≤ 4 + |t| := by
      calc ‖c‖ ≤ ‖(4 : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
        _ = 4 + |t| := by simp
    refine ⟨?_, ?_, ?_⟩
    · have := neg_abs_le (z.re - 4); linarith
    · have := abs_sub_abs_le_abs_sub t z.im
      rw [abs_sub_comm t] at this
      linarith
    · linarith
  have hne1 : ∀ z ∈ ball c R, z ≠ 1 := by
    intro z hz h
    have := (hgeo z hz).2.1
    rw [h] at this
    norm_num at this
  have hdiff : DifferentiableOn ℂ riemannZeta (ball c R) := fun z hz =>
    (differentiableAt_riemannZeta (hne1 z hz)).differentiableWithinAt
  have hnz : ∀ z ∈ ball c R, riemannZeta z ≠ 0 := by
    intro z hz h0
    have hre := (hgeo z hz).1
    have htriv : ¬∃ n : ℕ, z = -2 * (n + 1) := by
      rintro ⟨n, hn⟩
      rw [hn] at hre
      simp at hre
      linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    have := hRH z h0 htriv (hne1 z hz)
    linarith
  obtain ⟨g, hgd, hgc, hge⟩ := exists_log hdiff hnz
  have hgre : ∀ z ∈ ball c R, (g z).re = Real.log ‖riemannZeta z‖ := by
    intro z hz
    rw [← hge z hz, Complex.norm_exp, Real.log_exp]
  have h2R : (2 : ℝ) ≤ R := by linarith
  have hsub2 : ball c 2 ⊆ ball c R := ball_subset_ball h2R
  have hre2 : ∀ z ∈ ball c 2, 2 ≤ z.re := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    have h1 : |(z - c).re| ≤ ‖z - c‖ := Complex.abs_re_le_norm _
    rw [sub_re, hcre] at h1
    have := neg_abs_le (z.re - 4); linarith
  have hclose : ∀ z ∈ ball c 2, ‖riemannZeta z - 1‖ ≤ 2 / 3 := fun z hz =>
    (norm_riemannZeta_sub_one_le (hre2 z hz)).trans pi_sq_div_six_sub_one_le
  have hslit : ∀ z ∈ ball c 2, riemannZeta z ∈ Complex.slitPlane := by
    intro z hz
    refine Or.inl ?_
    have h1 : |(riemannZeta z - 1).re| ≤ ‖riemannZeta z - 1‖ := Complex.abs_re_le_norm _
    have h2 := hclose z hz
    rw [sub_re, one_re] at h1
    have := neg_abs_le ((riemannZeta z).re - 1)
    linarith
  have hglog : ∀ z ∈ ball c 2, g z = Complex.log (riemannZeta z) :=
    eq_log_of_slitPlane (hdiff.mono hsub2) hslit (fun z hz => hgd z (hsub2 hz)) hgc
  have hg6 : ∀ z ∈ ball c 2, ‖g z‖ ≤ 6 := by
    intro z hz
    rw [hglog z hz]
    exact norm_log_le_six (hclose z hz)
  have hcmem : c ∈ ball c 2 := mem_ball_self (by norm_num)
  set M : ℝ := 3 * Real.log |t| with hM
  have hMpos : 0 < M := by positivity
  have hreM : ∀ z ∈ ball c R, (g z).re ≤ M := by
    intro z hz
    obtain ⟨hzre, hzim, hzn⟩ := hgeo z hz
    have hzpos : 0 < z.re := by linarith
    have hb := norm_riemannZeta_le hzpos (hne1 z hz)
    have hz1 : 1 / 2 ≤ ‖z - 1‖ := by
      have := Complex.abs_im_le_norm (z - 1)
      rw [sub_im, one_im, sub_zero] at this
      linarith
    have hb1 : 1 / ‖z - 1‖ ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have hb2 : ‖z‖ / z.re ≤ 2 * (|t| + 8) := by
      rw [div_le_iff₀ hzpos]
      nlinarith [norm_nonneg z]
    have hζ : ‖riemannZeta z‖ ≤ 7 * |t| := by linarith
    rw [hgre z hz]
    have hpos : 0 < ‖riemannZeta z‖ := norm_pos_iff.mpr (hnz z hz)
    calc Real.log ‖riemannZeta z‖ ≤ Real.log (7 * |t|) := Real.log_le_log hpos hζ
      _ = Real.log 7 + Real.log |t| := Real.log_mul (by norm_num) ht0.ne'
      _ ≤ M := by
        have h7 : Real.log 7 ≤ 2 * Real.log |t| := by
          rw [← Real.log_rpow ht0]
          apply Real.log_le_log (by norm_num)
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          nlinarith
        linarith
  set M₃ : ℝ := 252 / δ * Real.log |t| with hM₃
  have hBC : ∀ z, ‖z - c‖ = r₃ → ‖g z‖ ≤ M₃ := by
    intro z hz
    have hRpos : 0 < R := by linarith
    have hfd : DifferentiableOn ℂ (fun w => g (c + w)) (ball 0 R) := by
      intro w hw
      have hw' : c + w ∈ ball c R := by
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left]; simpa using hw
      exact ((hgd _ hw').differentiableAt.comp w
        ((differentiableAt_const c).add differentiableAt_id)).differentiableWithinAt
    have hmaps : Set.MapsTo (fun w => g (c + w)) (ball 0 R) {z | z.re ≤ M} := by
      intro w hw
      have hw' : c + w ∈ ball c R := by
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left]; simpa using hw
      exact hreM _ hw'
    have hzmem : z - c ∈ ball (0 : ℂ) R := by
      rw [mem_ball, dist_zero_right, hz]; linarith
    have key := Complex.borelCaratheodory hMpos hfd hmaps hRpos hzmem
    simp only [add_sub_cancel, add_zero] at key
    rw [hz] at key
    have hgc6 : ‖g c‖ ≤ 6 := hg6 c hcmem
    have hRr : R - r₃ = δ / 4 := by rw [hR, hr₃]; ring
    rw [hRr] at key
    calc ‖g z‖ ≤ 2 * M * r₃ / (δ / 4) + ‖g c‖ * (R + r₃) / (δ / 4) := key
      _ ≤ 2 * M * (7 / 2) / (δ / 4) + 6 * 7 / (δ / 4) := by
        gcongr <;> linarith
      _ = (84 * Real.log |t| + 168) / δ := by rw [hM]; field_simp; ring
      _ ≤ M₃ := by
        rw [hM₃, div_mul_eq_mul_div]
        gcongr
        linarith
  set z : ℂ := σ + t * I with hz
  have hzc : ‖z - c‖ = 4 - σ := by
    have : z - c = ((σ - 4 : ℝ) : ℂ) := by rw [hz, hc]; push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    ring
  have hM₁ : ∀ w, ‖w - c‖ = 1 → ‖g w‖ ≤ 6 := by
    intro w hw
    exact hg6 w (by rw [mem_ball, dist_eq_norm, hw]; norm_num)
  have h3c := three_circles (r₁ := 1) (r₃ := r₃) (R := R) (M₁ := 6) (M₃ := M₃)
    one_pos (by linarith) (by linarith)
    (fun w hw => (hgd w hw).differentiableAt.differentiableWithinAt) hM₁ hBC
    (z := z) (by rw [hzc]; linarith) (by rw [hzc]; linarith)
  rw [hzc, Real.log_one, sub_zero, sub_zero] at h3c
  set θ : ℝ := Real.log (4 - σ) / Real.log r₃ with hθ
  have hθ0 : 0 ≤ θ := div_nonneg (Real.log_nonneg (by linarith)) hl2.le
  have hθa : θ ≤ a := by
    rw [hθ, ha_def]
    exact div_le_div_of_nonneg_right (Real.log_le_log (by linarith) (by linarith)) hl2.le
  have hM₃1 : 1 ≤ M₃ := by
    rw [hM₃]
    have : 1 ≤ 252 / δ := by rw [le_div_iff₀ hδ0]; linarith
    nlinarith
  have h6 : (6 : ℝ) ^ (1 - θ) ≤ 6 := by
    calc (6 : ℝ) ^ (1 - θ) ≤ 6 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 6 := Real.rpow_one 6
  have hMa : M₃ ^ θ ≤ (252 / δ) ^ a * Real.log |t| ^ a := by
    calc M₃ ^ θ ≤ M₃ ^ a := Real.rpow_le_rpow_of_exponent_le hM₃1 hθa
      _ = (252 / δ) ^ a * Real.log |t| ^ a := by
        rw [hM₃, Real.mul_rpow (by positivity) (by linarith)]
  have hgz : ‖g z‖ ≤ 6 * (252 / δ) ^ a * Real.log |t| ^ a := by
    calc ‖g z‖ ≤ 6 ^ (1 - θ) * M₃ ^ θ := h3c
      _ ≤ 6 * ((252 / δ) ^ a * Real.log |t| ^ a) := by
        gcongr
      _ = 6 * (252 / δ) ^ a * Real.log |t| ^ a := by ring
  have hzR : z ∈ ball c R := by
    rw [mem_ball, dist_eq_norm, hzc]; linarith
  rw [← hge z hzR, ← Complex.exp_neg, Complex.norm_exp]
  exact Real.exp_le_exp.mpr ((Complex.re_le_norm (-g z)).trans (by simpa using hgz))

/-- Under RH, the reciprocal bound `‖ζ(σ + it)⁻¹‖ ≤ |t| ^ ε` holds uniformly for
`1/2 + δ ≤ σ ≤ 1` and large `|t|`. -/
private theorem inv_lindelof_right (hRH : RiemannHypothesis) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t₁ : ℝ, 4 ≤ t₁ ∧ ∀ σ t : ℝ, 1 / 2 + δ ≤ σ → σ ≤ 1 → t₁ ≤ |t| →
      ‖(riemannZeta (σ + t * I))⁻¹‖ ≤ |t| ^ ε := by
  obtain ⟨K, a, ha1, hK⟩ := norm_inv_riemannZeta_le_exp hRH hδ0 hδ1
  set L₀ : ℝ := max 1 ((|K| / ε) ^ (1 / (1 - a))) with hL₀
  refine ⟨max 4 (Real.exp L₀), le_max_left _ _, ?_⟩
  intro σ t hσ1 hσ2 ht
  have ht4 : 4 ≤ |t| := (le_max_left _ _).trans ht
  have ht0 : 0 < |t| := by linarith
  have hL : L₀ ≤ Real.log |t| := by
    rw [Real.le_log_iff_exp_le ht0]; exact (le_max_right _ _).trans ht
  have hL1 : 1 ≤ Real.log |t| := (le_max_left _ _).trans hL
  refine (hK σ t hσ1 hσ2 ht4).trans ?_
  rw [Real.rpow_def_of_pos ht0]
  apply Real.exp_le_exp.mpr
  set L := Real.log |t| with hLdef
  have hLpos : 0 < L := by linarith
  have h1a : 0 < 1 - a := by linarith
  have hpow : |K| / ε ≤ L ^ (1 - a) := by
    have : (|K| / ε) = ((|K| / ε) ^ (1 / (1 - a))) ^ (1 - a) := by
      rw [← Real.rpow_mul (by positivity), one_div_mul_cancel h1a.ne', Real.rpow_one]
    rw [this]
    exact Real.rpow_le_rpow (by positivity) ((le_max_right _ _).trans hL) h1a.le
  have hK' : |K| ≤ ε * L ^ (1 - a) := by rwa [div_le_iff₀ hε, mul_comm] at hpow
  have hLa : 0 ≤ L ^ a := Real.rpow_nonneg hLpos.le a
  calc K * L ^ a ≤ |K| * L ^ a := mul_le_mul_of_nonneg_right (le_abs_self K) hLa
    _ ≤ (ε * L ^ (1 - a)) * L ^ a := mul_le_mul_of_nonneg_right hK' hLa
    _ = L * ε := by
      rw [mul_assoc, ← Real.rpow_add hLpos, sub_add_cancel, Real.rpow_one, mul_comm]

end Lindelof

@[expose] public section

/-- **Bound for $1/\zeta$ from the Riemann hypothesis.** Assume the Riemann hypothesis, and let
$1/2 < \sigma \le 1$ and $\varepsilon > 0$ be real. Then there are real constants $C$ and $t_0$,
depending on $\sigma$ and $\varepsilon$, such that $|1/\zeta(\sigma + it)| \le C |t|^{\varepsilon}$
for every real $t$ with $|t| \ge t_0$.

Source: Kampamolla Venkatasubbareddy and Ayyadurai Sankaranarayanan, *On the
Distribution of the Restricted Sequence of Integers 2^{ω(n)}*, INTEGERS 24
(2024), Article A110, Lemma 8 (`integers-2024-A110-lem-8`). -/
public theorem inv_zeta_le_rpow_of_riemannHypothesis (hRH : RiemannHypothesis)
    (σ : ℝ) (hσ : 1 / 2 < σ) (hσ1 : σ ≤ 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ C t₀ : ℝ, ∀ t : ℝ, t₀ ≤ |t| → ‖(riemannZeta (σ + t * I))⁻¹‖ ≤ C * |t| ^ ε := by
  let δ : ℝ := min (σ - 1 / 2) (1 / 4)
  have hδ0 : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ1 : δ ≤ 1 / 4 := min_le_right _ _
  have hδσ : 1 / 2 + δ ≤ σ := by
    have := min_le_left (σ - 1 / 2) (1 / 4)
    linarith
  obtain ⟨t₁, _, ht₁⟩ := inv_lindelof_right hRH hδ0 hδ1 hε
  refine ⟨1, t₁, fun t ht => ?_⟩
  simpa using ht₁ σ t hδσ hσ1 ht

end

end MetaMathlibExt
