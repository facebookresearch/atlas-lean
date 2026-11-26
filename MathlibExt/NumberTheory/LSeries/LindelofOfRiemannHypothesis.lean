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
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.PSeriesComplex
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.ZetaValues

/-!
# The Lindelöf bound for the Riemann zeta function under the Riemann hypothesis

Assuming the Riemann hypothesis, `MetaMathlibExt.zeta_le_rpow_of_riemannHypothesis` proves that
for every `ε > 0` there are constants `C` and `t₀` with `‖ζ(σ + it)‖ ≤ C |t| ^ ε` for all
`1 / 2 ≤ σ ≤ 1` and `|t| ≥ t₀`.

The proof is the classical argument through a holomorphic logarithm of `ζ`.

* For `0 < re s` and `s ≠ 1` we prove `ζ(s) = s / (s - 1) - s ∫_1^∞ {x} x^{-s-1} dx` (by the
  identity theorem from the Dirichlet series), which gives the polynomial bound
  `‖ζ(s)‖ ≤ 1 / ‖s - 1‖ + 1 + ‖s‖ / re s`.
* Under the Riemann hypothesis `ζ` has no zeros in `re s > 1 / 2`, so it has a holomorphic
  logarithm `g` on the disc of radius `7 / 2 - δ / 4` about `4 + it` (a primitive of `ζ' / ζ`).
  The Borel–Carathéodory theorem turns the upper bound `re g = log ‖ζ‖ ≪ log |t|` into
  `‖g‖ ≪ log |t| / δ` on a slightly smaller circle; on the circle of radius `1`, where
  `re s ≥ 3`, `g` is the principal logarithm of `ζ` and is bounded. Hadamard's three-circles
  theorem (from Mathlib's three-lines theorem through `w ↦ 4 + it + exp w`) interpolates the two
  bounds to `‖g(σ + it)‖ ≪ (log |t|) ^ a` with `a < 1`, uniformly for `1 / 2 + δ ≤ σ ≤ 1`, hence
  `‖ζ(σ + it)‖ ≤ exp (‖g‖) ≤ |t| ^ ε` for large `|t|`.
* Near the critical line the functional equation, together with the bound
  `‖Γ(1 / 2 + δ + it) cos (π (1 / 2 + δ + it) / 2)‖ ≪ |t| ^ δ` (three lines on the strip
  `1 / 2 ≤ re z ≤ 3 / 2`, with bounds on its edges from the reflection formula), bounds `ζ`
  on the line `re s = 1 / 2 - δ` by `|t| ^ (δ + ε)`, and the three-lines theorem on the strip
  `1 / 2 - δ ≤ re s ≤ 1 / 2 + δ`, applied to `ζ(s) exp ((s - it₀) ^ 2)`, covers
  `1 / 2 ≤ σ ≤ 1 / 2 + δ`.
-/

open Complex

namespace MetaMathlibExt
namespace zeta_le_rpow_of_riemannHypothesis

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
  -- rewrite the integrand
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

section GammaBound

/-- `‖cos w‖ ≤ cosh (im w)`. -/
private theorem norm_cos_le_cosh (w : ℂ) : ‖Complex.cos w‖ ≤ Real.cosh w.im := by
  have h2 : Complex.cos w = (Complex.exp (w * I) + Complex.exp (-w * I)) / 2 := by
    rw [← Complex.two_cos]; ring
  have e1 : ‖Complex.exp (w * I)‖ = Real.exp (-w.im) := by
    rw [Complex.norm_exp]; simp
  have e2 : ‖Complex.exp (-w * I)‖ = Real.exp w.im := by
    rw [Complex.norm_exp]; simp
  rw [h2, Real.cosh_eq, norm_div, Complex.norm_two]
  gcongr
  calc ‖Complex.exp (w * I) + Complex.exp (-w * I)‖
      ≤ ‖Complex.exp (w * I)‖ + ‖Complex.exp (-w * I)‖ := norm_add_le _ _
    _ = Real.exp w.im + Real.exp (-w.im) := by rw [e1, e2]; ring

/-- `cosh x ≤ exp |x|`. -/
private theorem cosh_le_exp_abs (x : ℝ) : Real.cosh x ≤ Real.exp |x| := by
  rw [Real.cosh_eq]
  have h1 : Real.exp x ≤ Real.exp |x| := Real.exp_le_exp.mpr (le_abs_self x)
  have h2 : Real.exp (-x) ≤ Real.exp |x| := Real.exp_le_exp.mpr (neg_le_abs x)
  linarith

/-- `cosh (x / 2) ^ 2 ≤ cosh x`. -/
private theorem cosh_half_sq_le (x : ℝ) : Real.cosh (x / 2) ^ 2 ≤ Real.cosh x := by
  have h := Real.cosh_two_mul (x / 2)
  have h2 := Real.cosh_sq (x / 2)
  have h3 := Real.one_le_cosh x
  rw [show 2 * (x / 2) = x by ring] at h
  nlinarith

/-- `‖Γ(s)‖ ≤ Γ(re s)` for `re s > 0`. -/
private theorem norm_Gamma_le_Gamma_re {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Real.Gamma_eq_integral hs, Complex.GammaIntegral]
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

/-- On the line `re w = 1/2`: `‖Γ(w)‖ cosh(π im w / 2) ≤ 2`. -/
private theorem norm_Gamma_mul_cosh_half_le {w : ℂ} (hw : w.re = 1 / 2) :
    ‖Complex.Gamma w‖ * Real.cosh (Real.pi * w.im / 2) ≤ 2 := by
  have h1 : 1 - w = (starRingEnd ℂ) w := by
    apply Complex.ext
    · simp [hw]; norm_num
    · simp
  have hrefl := Complex.Gamma_mul_Gamma_one_sub w
  rw [h1, Complex.Gamma_conj] at hrefl
  have hsin : Complex.sin (↑Real.pi * w) = ↑(Real.cosh (Real.pi * w.im)) := by
    have : ↑Real.pi * w = (↑(Real.pi * w.im) : ℂ) * I + ↑Real.pi / 2 := by
      apply Complex.ext
      · simp [hw]; ring
      · simp
    rw [this, Complex.sin_add_pi_div_two, Complex.cos_mul_I, Complex.ofReal_cosh]
  have hn := congrArg norm hrefl
  rw [norm_mul, Complex.norm_conj, hsin, norm_div, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
    abs_of_pos (Real.cosh_pos _)] at hn
  have hc := Real.cosh_pos (Real.pi * w.im)
  have hsq : ‖Complex.Gamma w‖ ^ 2 * Real.cosh (Real.pi * w.im) = Real.pi := by
    rw [sq, hn]; field_simp
  have hhalf := cosh_half_sq_le (Real.pi * w.im)
  have hpi := Real.pi_le_four
  have hG := norm_nonneg (Complex.Gamma w)
  have hch := Real.cosh_pos (Real.pi * w.im / 2)
  have key : (‖Complex.Gamma w‖ * Real.cosh (Real.pi * w.im / 2)) ^ 2 ≤ 4 := by
    calc (‖Complex.Gamma w‖ * Real.cosh (Real.pi * w.im / 2)) ^ 2
        = ‖Complex.Gamma w‖ ^ 2 * Real.cosh (Real.pi * w.im / 2) ^ 2 := by ring
      _ ≤ ‖Complex.Gamma w‖ ^ 2 * Real.cosh (Real.pi * w.im) := by gcongr
      _ = Real.pi := hsq
      _ ≤ 4 := hpi
  nlinarith [mul_nonneg hG hch.le]

/-- On the line `re z = 1/2`: `‖Γ(z) cos(π z / 2)‖ ≤ 2`. -/
private theorem norm_Gamma_mul_cos_le_of_re_eq_half {z : ℂ} (hz : z.re = 1 / 2) :
    ‖Complex.Gamma z * Complex.cos (↑Real.pi * z / 2)‖ ≤ 2 := by
  rw [norm_mul]
  have hc := norm_cos_le_cosh (↑Real.pi * z / 2)
  have him : (↑Real.pi * z / 2 : ℂ).im = Real.pi * z.im / 2 := by simp
  rw [him] at hc
  calc ‖Complex.Gamma z‖ * ‖Complex.cos (↑Real.pi * z / 2)‖
      ≤ ‖Complex.Gamma z‖ * Real.cosh (Real.pi * z.im / 2) := by gcongr
    _ ≤ 2 := norm_Gamma_mul_cosh_half_le hz

/-- On the line `re z = 3/2`: `‖Γ(z) cos(π z / 2)‖ ≤ 1 + 2 |im z|`. -/
private theorem norm_Gamma_mul_cos_le_of_re_eq_three_half {z : ℂ} (hz : z.re = 3 / 2) :
    ‖Complex.Gamma z * Complex.cos (↑Real.pi * z / 2)‖ ≤ 1 + 2 * |z.im| := by
  set w := z - 1 with hw
  have hwre : w.re = 1 / 2 := by simp [hw, hz]; norm_num
  have hwim : w.im = z.im := by simp [hw]
  have hw0 : w ≠ 0 := by
    intro h; rw [h] at hwre; simp at hwre
  have hz' : z = w + 1 := by simp [hw]
  have hG : Complex.Gamma z = w * Complex.Gamma w := by
    rw [hz', Complex.Gamma_add_one w hw0]
  have hc := norm_cos_le_cosh (↑Real.pi * z / 2)
  have him : (↑Real.pi * z / 2 : ℂ).im = Real.pi * w.im / 2 := by simp [hwim]
  rw [him] at hc
  have hwn : ‖w‖ ≤ 1 / 2 + |z.im| := by
    calc ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
      _ = 1 / 2 + |z.im| := by rw [hwre, hwim]; norm_num
  have hK := norm_Gamma_mul_cosh_half_le hwre
  have hK0 : 0 ≤ ‖Complex.Gamma w‖ * Real.cosh (Real.pi * w.im / 2) :=
    mul_nonneg (norm_nonneg _) (Real.cosh_pos _).le
  rw [norm_mul, hG, norm_mul]
  calc ‖w‖ * ‖Complex.Gamma w‖ * ‖Complex.cos (↑Real.pi * z / 2)‖
      ≤ ‖w‖ * (‖Complex.Gamma w‖ * Real.cosh (Real.pi * w.im / 2)) := by
        rw [mul_assoc]; gcongr
    _ ≤ (1 / 2 + |z.im|) * 2 := by
        apply mul_le_mul hwn hK hK0 (by positivity)
    _ = 1 + 2 * |z.im| := by ring

/-- `‖Γ(1/2 + η + it) cos (π (1/2 + η + it) / 2)‖ ≤ C |t| ^ η` for `0 ≤ η ≤ 1` and `|t| ≥ 1`,
by the three-lines theorem on `1/2 ≤ re z ≤ 3/2` with a Gaussian factor localising at
height `t`. -/
private theorem norm_Gamma_mul_cos_le {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ |t| →
      ‖Complex.Gamma (((1 / 2 + η : ℝ) : ℂ) + t * Complex.I) *
        Complex.cos (Real.pi * (((1 / 2 + η : ℝ) : ℂ) + t * Complex.I) / 2)‖ ≤ C * |t| ^ η := by
  -- a bound for the real Gamma function on `[1/2, 3/2]`
  obtain ⟨B, hB⟩ : ∃ B, ∀ σ ∈ Set.Icc (1 / 2 : ℝ) (3 / 2), ‖Real.Gamma σ‖ ≤ B := by
    apply isCompact_Icc.exists_bound_of_continuousOn
    intro σ hσ
    apply ContinuousAt.continuousWithinAt
    apply (Real.differentiableAt_Gamma _).continuousAt
    intro m hm
    have h0 : (0 : ℝ) < σ := by linarith [hσ.1]
    have h1 : (-(m : ℝ)) ≤ 0 := by simp
    linarith
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 1 ⟨by norm_num, by norm_num⟩)
  set a : ℝ := 2 * Real.exp (1 / 4) with ha_def
  set b : ℝ := 4 * Real.exp (9 / 4) with hb_def
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  refine ⟨a + b, fun t₀ ht₀ => ?_⟩
  have ht₀pos : 0 < |t₀| := lt_of_lt_of_le one_pos ht₀
  set L := Real.log |t₀| with hL
  have hL0 : 0 ≤ L := Real.log_nonneg ht₀
  set F : ℂ → ℂ := fun z => Complex.Gamma z * Complex.cos (↑Real.pi * z / 2) *
    Complex.exp (-(z - 1 / 2) * ↑L) * Complex.exp ((z - ↑t₀ * I) ^ 2) with hF
  have hw1 : ∀ z : ℂ, ‖Complex.exp (-(z - 1 / 2) * ↑L)‖ = Real.exp (-(z.re - 1 / 2) * L) := by
    intro z; rw [Complex.norm_exp]; congr 1; simp
  have hw2 : ∀ z : ℂ,
      ‖Complex.exp ((z - ↑t₀ * I) ^ 2)‖ = Real.exp (z.re ^ 2 - (z.im - t₀) ^ 2) := by
    intro z; rw [Complex.norm_exp]; congr 1; simp [sq]
  have hFn : ∀ z : ℂ, ‖F z‖ = ‖Complex.Gamma z * Complex.cos (↑Real.pi * z / 2)‖ *
      Real.exp (-(z.re - 1 / 2) * L) * Real.exp (z.re ^ 2 - (z.im - t₀) ^ 2) := by
    intro z; simp only [hF, norm_mul, hw1, hw2]
  -- differentiability on the right half-plane
  have hdiff : DifferentiableOn ℂ F {z : ℂ | 0 < z.re} := by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    have hG : DifferentiableAt ℂ Complex.Gamma z := by
      apply Complex.differentiableAt_Gamma
      intro m hm
      have h0 : (0 : ℝ) < z.re := hz
      rw [hm] at h0
      simp at h0
      linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have h2 : DifferentiableAt ℂ (fun z : ℂ => Complex.cos (↑Real.pi * z / 2)) z := by fun_prop
    have h3 : DifferentiableAt ℂ (fun z : ℂ => Complex.exp (-(z - 1 / 2) * ↑L)) z := by fun_prop
    have h4 : DifferentiableAt ℂ (fun z : ℂ => Complex.exp ((z - ↑t₀ * I) ^ 2)) z := by fun_prop
    exact ((hG.mul h2).mul h3).mul h4
  have hclosure : closure (Complex.HadamardThreeLines.verticalStrip (1 / 2) (3 / 2)) =
      Complex.HadamardThreeLines.verticalClosedStrip (1 / 2) (3 / 2) := by
    simp only [Complex.HadamardThreeLines.verticalStrip,
      Complex.HadamardThreeLines.verticalClosedStrip]
    rw [closure_preimage_re, closure_Ioo (by norm_num)]
  have hd : DiffContOnCl ℂ F (Complex.HadamardThreeLines.verticalStrip (1 / 2) (3 / 2)) := by
    apply DifferentiableOn.diffContOnCl
    rw [hclosure]
    apply hdiff.mono
    intro z hz
    simp only [Complex.HadamardThreeLines.verticalClosedStrip, Set.mem_preimage,
      Set.mem_Icc] at hz
    change 0 < z.re
    linarith [hz.1]
  -- boundedness on the closed strip
  have hBdd : BddAbove ((norm ∘ F) '' Complex.HadamardThreeLines.verticalClosedStrip
      (1 / 2) (3 / 2)) := by
    refine ⟨B * Real.exp (9 / 4) * Real.exp (2 * |t₀| + 1), ?_⟩
    rintro y ⟨z, hz, rfl⟩
    simp only [Complex.HadamardThreeLines.verticalClosedStrip, Set.mem_preimage,
      Set.mem_Icc] at hz
    simp only [Function.comp, hFn]
    have hre0 : 0 < z.re := by linarith [hz.1]
    have h1 : ‖Complex.Gamma z * Complex.cos (↑Real.pi * z / 2)‖ ≤
        B * Real.exp (2 * |z.im|) := by
      rw [norm_mul]
      have hg := norm_Gamma_le_Gamma_re hre0
      have hgB : Real.Gamma z.re ≤ B := by
        have := hB z.re ⟨hz.1, hz.2⟩
        exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using this)
      have hc := norm_cos_le_cosh (↑Real.pi * z / 2)
      have him : (↑Real.pi * z / 2 : ℂ).im = Real.pi * z.im / 2 := by simp
      rw [him] at hc
      have hc2 : Real.cosh (Real.pi * z.im / 2) ≤ Real.exp (2 * |z.im|) := by
        refine (cosh_le_exp_abs _).trans (Real.exp_le_exp.mpr ?_)
        rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_two]
        have := Real.pi_le_four
        have := abs_nonneg z.im
        nlinarith
      exact mul_le_mul (hg.trans hgB) (hc.trans hc2) (norm_nonneg _) hB0
    have h2 : Real.exp (-(z.re - 1 / 2) * L) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ z.re - 1 / 2 := by linarith [hz.1]
      nlinarith
    have h3 : Real.exp (z.re ^ 2 - (z.im - t₀) ^ 2) ≤
        Real.exp (9 / 4) * Real.exp (-(z.im - t₀) ^ 2) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith [hz.1, hz.2]
    have h4 : Real.exp (2 * |z.im|) * Real.exp (-(z.im - t₀) ^ 2) ≤
        Real.exp (2 * |t₀| + 1) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
      have := abs_sub_abs_le_abs_sub z.im t₀
      have hu := sq_abs (z.im - t₀)
      nlinarith [abs_nonneg (z.im - t₀), sq_nonneg (|z.im - t₀| - 1)]
    calc ‖Complex.Gamma z * Complex.cos (↑Real.pi * z / 2)‖ *
          Real.exp (-(z.re - 1 / 2) * L) * Real.exp (z.re ^ 2 - (z.im - t₀) ^ 2)
        ≤ (B * Real.exp (2 * |z.im|)) * 1 *
            (Real.exp (9 / 4) * Real.exp (-(z.im - t₀) ^ 2)) := by
          gcongr
      _ = B * Real.exp (9 / 4) * (Real.exp (2 * |z.im|) * Real.exp (-(z.im - t₀) ^ 2)) := by
          ring
      _ ≤ B * Real.exp (9 / 4) * Real.exp (2 * |t₀| + 1) := by gcongr
  -- the bounds on the two boundary lines
  have ha : ∀ z ∈ re ⁻¹' {(1 / 2 : ℝ)}, ‖F z‖ ≤ a := by
    intro z hz
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hz
    rw [hFn, hz]
    have h1 := norm_Gamma_mul_cos_le_of_re_eq_half hz
    have h3 : Real.exp ((1 / 2 : ℝ) ^ 2 - (z.im - t₀) ^ 2) ≤ Real.exp (1 / 4) := by
      apply Real.exp_le_exp.mpr; nlinarith [sq_nonneg (z.im - t₀)]
    calc ‖Complex.Gamma z * Complex.cos (↑Real.pi * z / 2)‖ * Real.exp (-(1 / 2 - 1 / 2) * L) *
          Real.exp ((1 / 2 : ℝ) ^ 2 - (z.im - t₀) ^ 2)
        = ‖Complex.Gamma z * Complex.cos (↑Real.pi * z / 2)‖ *
            Real.exp ((1 / 2 : ℝ) ^ 2 - (z.im - t₀) ^ 2) := by simp
      _ ≤ 2 * Real.exp (1 / 4) := by gcongr
  have hb : ∀ z ∈ re ⁻¹' {(3 / 2 : ℝ)}, ‖F z‖ ≤ b := by
    intro z hz
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hz
    rw [hFn, hz]
    have h1 := norm_Gamma_mul_cos_le_of_re_eq_three_half hz
    have hexpL : Real.exp (-(3 / 2 - 1 / 2) * L) = |t₀|⁻¹ := by
      rw [show -(3 / 2 - 1 / 2 : ℝ) * L = -L by ring, Real.exp_neg, hL, Real.exp_log ht₀pos]
    rw [hexpL]
    set u := |z.im - t₀| with hu
    have hu0 : 0 ≤ u := abs_nonneg _
    have hu2 : (z.im - t₀) ^ 2 = u ^ 2 := (sq_abs _).symm
    have htri : |z.im| ≤ |t₀| + u := by
      have := abs_sub_abs_le_abs_sub z.im t₀
      linarith
    have hnum : 1 + 2 * |z.im| ≤ |t₀| * (3 + 2 * u) := by nlinarith
    have hexp : (3 + 2 * u) * Real.exp (-u ^ 2) ≤ 4 := by
      have h := Real.add_one_le_exp (u ^ 2)
      have hpos := Real.exp_pos (u ^ 2)
      have hmul : Real.exp (-u ^ 2) * Real.exp (u ^ 2) = 1 := by
        rw [← Real.exp_add]; simp
      have hpos' := Real.exp_pos (-u ^ 2)
      nlinarith [sq_nonneg (2 * u - 1 / 2)]
    rw [hu2]
    have hsplit : Real.exp ((3 / 2 : ℝ) ^ 2 - u ^ 2) = Real.exp (9 / 4) * Real.exp (-u ^ 2) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hsplit]
    have hinv : 0 < |t₀|⁻¹ := inv_pos.mpr ht₀pos
    calc ‖Complex.Gamma z * Complex.cos (↑Real.pi * z / 2)‖ * |t₀|⁻¹ *
          (Real.exp (9 / 4) * Real.exp (-u ^ 2))
        ≤ (|t₀| * (3 + 2 * u)) * |t₀|⁻¹ * (Real.exp (9 / 4) * Real.exp (-u ^ 2)) := by
          gcongr; exact h1.trans hnum
      _ = Real.exp (9 / 4) * ((3 + 2 * u) * Real.exp (-u ^ 2)) := by
          field_simp
      _ ≤ Real.exp (9 / 4) * 4 := by gcongr
      _ = b := by rw [hb_def]; ring
  -- apply the three lines theorem at `z₀ = 1/2 + η + i t₀`
  set z₀ : ℂ := ((1 / 2 + η : ℝ) : ℂ) + t₀ * I with hz₀_def
  have hz₀re : z₀.re = 1 / 2 + η := by simp [hz₀_def]
  have hz₀im : z₀.im = t₀ := by simp [hz₀_def]
  have hz₀ : z₀ ∈ Complex.HadamardThreeLines.verticalClosedStrip (1 / 2) (3 / 2) := by
    simp only [Complex.HadamardThreeLines.verticalClosedStrip, Set.mem_preimage, Set.mem_Icc,
      hz₀re]
    constructor <;> linarith
  have h3l := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
    (by norm_num) hz₀ hd hBdd ha hb
  have hθ : (z₀.re - 1 / 2) / (3 / 2 - 1 / 2) = η := by rw [hz₀re]; ring
  rw [hθ] at h3l
  have hamgm : a ^ (1 - η) * b ^ η ≤ (1 - η) * a + η * b :=
    Real.geom_mean_le_arith_mean2_weighted (by linarith) hη0 ha0 hb0 (by ring)
  have hab : (1 - η) * a + η * b ≤ a + b := by nlinarith
  rw [hFn, hz₀re, hz₀im] at h3l
  have hlast : Real.exp (0 : ℝ) ≤ Real.exp ((1 / 2 + η) ^ 2 - (t₀ - t₀) ^ 2) := by
    apply Real.exp_le_exp.mpr; nlinarith
  rw [Real.exp_zero] at hlast
  have hrpow : |t₀| ^ η = Real.exp (L * η) := by
    rw [Real.rpow_def_of_pos ht₀pos]
  have hexpη : Real.exp (-(1 / 2 + η - 1 / 2) * L) * Real.exp (L * η) = 1 := by
    rw [← Real.exp_add]; ring_nf; simp
  set H := ‖Complex.Gamma z₀ * Complex.cos (↑Real.pi * z₀ / 2)‖ with hH
  have hH0 : 0 ≤ H := norm_nonneg _
  have hE := Real.exp_pos (-(1 / 2 + η - 1 / 2) * L)
  have hE' := Real.exp_pos (L * η)
  have step : H * Real.exp (-(1 / 2 + η - 1 / 2) * L) ≤ a + b := by
    calc H * Real.exp (-(1 / 2 + η - 1 / 2) * L)
        = H * Real.exp (-(1 / 2 + η - 1 / 2) * L) * 1 := by ring
      _ ≤ H * Real.exp (-(1 / 2 + η - 1 / 2) * L) *
            Real.exp ((1 / 2 + η) ^ 2 - (t₀ - t₀) ^ 2) := by gcongr
      _ ≤ a ^ (1 - η) * b ^ η := h3l
      _ ≤ a + b := hamgm.trans hab
  rw [hrpow]
  calc H = H * Real.exp (-(1 / 2 + η - 1 / 2) * L) * Real.exp (L * η) := by
        rw [mul_assoc, hexpη, mul_one]
    _ ≤ (a + b) * Real.exp (L * η) := by gcongr

end GammaBound

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

/-- Under RH: for `1/2 + δ ≤ σ ≤ 1` and `4 ≤ |t|`, `‖ζ(σ + it)‖ ≤ exp (K (log |t|)^a)` with
`a < 1`. -/
private theorem norm_riemannZeta_le_exp (hRH : RiemannHypothesis) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1 / 4) :
    ∃ K a : ℝ, a < 1 ∧ ∀ σ t : ℝ, 1 / 2 + δ ≤ σ → σ ≤ 1 → 4 ≤ |t| →
      ‖riemannZeta (σ + t * I)‖ ≤ Real.exp (K * Real.log |t| ^ a) := by
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
  -- geometry of the disc `ball c R`
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
  -- `re g = log ‖ζ‖`
  have hgre : ∀ z ∈ ball c R, (g z).re = Real.log ‖riemannZeta z‖ := by
    intro z hz
    rw [← hge z hz, Complex.norm_exp, Real.log_exp]
  -- `g = log ∘ ζ` on `ball c 2`
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
  -- upper bound for `re g` on `ball c R`
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
  -- Borel–Carathéodory on `ball c R`
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
  -- three circles
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
  rw [← hge z hzR, Complex.norm_exp]
  exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans hgz)

/-- Under RH, the Lindelöf bound `‖ζ(σ + it)‖ ≤ |t| ^ ε` holds uniformly for
`1/2 + δ ≤ σ ≤ 1` and large `|t|`. -/
private theorem lindelof_right (hRH : RiemannHypothesis) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t₁ : ℝ, 4 ≤ t₁ ∧ ∀ σ t : ℝ, 1 / 2 + δ ≤ σ → σ ≤ 1 → t₁ ≤ |t| →
      ‖riemannZeta (σ + t * I)‖ ≤ |t| ^ ε := by
  obtain ⟨K, a, ha1, hK⟩ := norm_riemannZeta_le_exp hRH hδ0 hδ1
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

/-- `(1 + |u|) exp (-u²) ≤ 2`. -/
private theorem one_add_abs_mul_exp_neg_sq_le (u : ℝ) : (1 + |u|) * Real.exp (-u ^ 2) ≤ 2 := by
  have h1 : Real.exp (-u ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg u])
  have h3 : |u| ≤ Real.exp (u ^ 2) := by
    have := Real.add_one_le_exp (u ^ 2)
    nlinarith [sq_abs u, abs_nonneg u, sq_nonneg (|u| - 1)]
  have h2 : |u| * Real.exp (-u ^ 2) ≤ 1 := by
    rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _)]; linarith
  calc (1 + |u|) * Real.exp (-u ^ 2) = Real.exp (-u ^ 2) + |u| * Real.exp (-u ^ 2) := by ring
    _ ≤ 1 + 1 := add_le_add h1 h2
    _ = 2 := by norm_num

/-- For `|t₀| ≥ 1` and `0 ≤ κ ≤ 1`, `|t| ^ κ ≤ |t₀| ^ κ (1 + |t - t₀|)`. -/
private theorem abs_rpow_le {t t₀ κ : ℝ} (ht₀ : 1 ≤ |t₀|) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) :
    |t| ^ κ ≤ |t₀| ^ κ * (1 + |t - t₀|) := by
  have h1 : |t| ≤ |t₀| * (1 + |t - t₀|) := by
    have := abs_sub_abs_le_abs_sub t t₀
    nlinarith [mul_nonneg (sub_nonneg.mpr ht₀) (abs_nonneg (t - t₀))]
  calc |t| ^ κ ≤ (|t₀| * (1 + |t - t₀|)) ^ κ := Real.rpow_le_rpow (abs_nonneg _) h1 hκ0
    _ = |t₀| ^ κ * (1 + |t - t₀|) ^ κ := Real.mul_rpow (by linarith) (by positivity)
    _ ≤ |t₀| ^ κ * (1 + |t - t₀|) := by
      gcongr
      calc (1 + |t - t₀|) ^ κ ≤ (1 + |t - t₀|) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg (t - t₀)]) hκ1
        _ = 1 + |t - t₀| := Real.rpow_one _

/-- The modulus of the Gaussian factor `exp ((z - i t₀)²)`. -/
private theorem norm_exp_sq (z : ℂ) (t₀ : ℝ) :
    ‖Complex.exp ((z - t₀ * I) ^ 2)‖ = Real.exp (z.re ^ 2 - (z.im - t₀) ^ 2) := by
  rw [Complex.norm_exp]
  congr 1
  simp [sq, Complex.mul_re]

/-- Polynomial bound for `ζ` on the strip `1/4 ≤ re z ≤ 3/4`. -/
private theorem norm_riemannZeta_le_strip {z : ℂ} (h1 : 1 / 4 ≤ z.re) (h2 : z.re ≤ 3 / 4) :
    ‖riemannZeta z‖ ≤ 9 + 4 * |z.im| := by
  have hz0 : 0 < z.re := by linarith
  have hz1 : z ≠ 1 := by rintro rfl; norm_num at h2
  have hb := norm_riemannZeta_le hz0 hz1
  have hn1 : 1 / 4 ≤ ‖z - 1‖ := by
    have h := Complex.abs_re_le_norm (z - 1)
    rw [sub_re, one_re] at h
    have := neg_abs_le (z.re - 1)
    linarith
  have hzn : ‖z‖ ≤ 1 + |z.im| := by
    have := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_pos hz0] at this; linarith
  have hb1 : 1 / ‖z - 1‖ ≤ 4 := by rw [div_le_iff₀ (by linarith)]; linarith
  have hb2 : ‖z‖ / z.re ≤ 4 * (1 + |z.im|) := by
    rw [div_le_iff₀ hz0]
    nlinarith [norm_nonneg z, abs_nonneg z.im,
      mul_nonneg (abs_nonneg z.im) (by linarith : (0 : ℝ) ≤ z.re - 1 / 4)]
  linarith

/-- `x ^ (1 - θ) y ^ θ ≤ max x y` for `x, y ≥ 0` and `0 ≤ θ ≤ 1`. -/
private theorem rpow_mul_rpow_le_max {x y θ : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) : x ^ (1 - θ) * y ^ θ ≤ max x y := by
  have := Real.geom_mean_le_arith_mean2_weighted (sub_nonneg.mpr hθ1) hθ0 hx hy (by ring)
  calc x ^ (1 - θ) * y ^ θ ≤ (1 - θ) * x + θ * y := this
    _ ≤ (1 - θ) * max x y + θ * max x y :=
      add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith))
        (mul_le_mul_of_nonneg_left (le_max_right _ _) hθ0)
    _ = max x y := by ring

/-- Under RH, `‖ζ(σ + it)‖ ≤ C |t| ^ (δ + ε)` for `1/2 - δ ≤ σ ≤ 1/2 + δ` and large `|t|`: the
functional equation bounds `ζ` on `re s = 1/2 - δ`, and the three-lines theorem, applied to
`ζ(s) exp ((s - i t₀)²)`, interpolates. -/
private theorem lindelof_critical (hRH : RiemannHypothesis) {δ ε : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1 / 4) (hε : 0 < ε) (hδε : δ + ε ≤ 1) :
    ∃ C t₂ : ℝ, 1 ≤ t₂ ∧ ∀ σ t : ℝ, 1 / 2 - δ ≤ σ → σ ≤ 1 / 2 + δ → t₂ ≤ |t| →
      ‖riemannZeta (σ + t * I)‖ ≤ C * |t| ^ (δ + ε) := by
  obtain ⟨t₁, ht₁, hR⟩ := lindelof_right hRH hδ0 hδ1 hε
  obtain ⟨CΓ, hΓ⟩ := norm_Gamma_mul_cos_le hδ0.le (by linarith)
  set C' : ℝ := max CΓ 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  set κ : ℝ := δ + ε with hκ
  have hκ0 : 0 ≤ κ := by positivity
  refine ⟨12 * C' + 33 + 12 * t₁, t₁, by linarith, ?_⟩
  intro σ t₀ hσl hσu ht₀
  have ht₀1 : 1 ≤ |t₀| := by linarith
  have hpow1 : 1 ≤ |t₀| ^ κ := Real.one_le_rpow ht₀1 hκ0
  set l : ℝ := 1 / 2 - δ with hl
  set u : ℝ := 1 / 2 + δ with hu
  set F : ℂ → ℂ := fun z => riemannZeta z * Complex.exp ((z - t₀ * I) ^ 2) with hF
  have hFn : ∀ z : ℂ,
      ‖F z‖ = ‖riemannZeta z‖ * Real.exp (z.re ^ 2 - (z.im - t₀) ^ 2) := by
    intro z; simp only [hF, norm_mul, norm_exp_sq]
  have hE : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 3 / 4 →
      Real.exp (z.re ^ 2 - (z.im - t₀) ^ 2) ≤ 3 * Real.exp (-(z.im - t₀) ^ 2) := by
    intro z h0 h1
    rw [sub_eq_add_neg, Real.exp_add]
    gcongr
    calc Real.exp (z.re ^ 2) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by nlinarith)
      _ ≤ 3 := (Real.exp_one_lt_d9).le.trans (by norm_num)
  have hE1 : ∀ z : ℂ, Real.exp (-(z.im - t₀) ^ 2) ≤ 1 := fun z =>
    Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (z.im - t₀)])
  -- small heights: polynomial bound
  have hsmall : ∀ z : ℂ, 1 / 4 ≤ z.re → z.re ≤ 3 / 4 → |z.im| < t₁ →
      ‖F z‖ ≤ (27 + 12 * t₁) * |t₀| ^ κ := by
    intro z h1 h2 hs
    rw [hFn]
    have hζ : ‖riemannZeta z‖ ≤ 9 + 4 * t₁ := by
      have := norm_riemannZeta_le_strip h1 h2
      linarith
    calc ‖riemannZeta z‖ * Real.exp (z.re ^ 2 - (z.im - t₀) ^ 2)
        ≤ (9 + 4 * t₁) * (3 * 1) := by
          gcongr
          exact (hE z (by linarith) h2).trans (by gcongr; exact hE1 z)
      _ = (27 + 12 * t₁) * 1 := by ring
      _ ≤ (27 + 12 * t₁) * |t₀| ^ κ := by gcongr
  -- the right line
  have hright : ∀ z ∈ Complex.re ⁻¹' {u}, ‖F z‖ ≤ (33 + 12 * t₁) * |t₀| ^ κ := by
    intro z hz
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hz
    have hz1 : 1 / 4 ≤ z.re := by rw [hz]; linarith
    have hz2 : z.re ≤ 3 / 4 := by rw [hz]; linarith
    by_cases hs : t₁ ≤ |z.im|
    · have hζ : ‖riemannZeta z‖ ≤ |z.im| ^ ε := by
        have h := hR u z.im le_rfl (by linarith) hs
        rwa [← hz, Complex.re_add_im] at h
      rw [hFn]
      calc ‖riemannZeta z‖ * Real.exp (z.re ^ 2 - (z.im - t₀) ^ 2)
          ≤ |z.im| ^ ε * (3 * Real.exp (-(z.im - t₀) ^ 2)) := by
            gcongr
            exact hE z (by linarith) hz2
        _ ≤ (|t₀| ^ ε * (1 + |z.im - t₀|)) * (3 * Real.exp (-(z.im - t₀) ^ 2)) := by
            gcongr
            exact abs_rpow_le ht₀1 hε.le (by linarith)
        _ = 3 * |t₀| ^ ε * ((1 + |z.im - t₀|) * Real.exp (-(z.im - t₀) ^ 2)) := by ring
        _ ≤ 3 * |t₀| ^ ε * 2 := by gcongr; exact one_add_abs_mul_exp_neg_sq_le _
        _ ≤ 3 * |t₀| ^ κ * 2 := by
            gcongr
            linarith
        _ ≤ (33 + 12 * t₁) * |t₀| ^ κ := by nlinarith
    · push Not at hs
      exact (hsmall z hz1 hz2 hs).trans (by gcongr; linarith)
  -- the left line, through the functional equation
  have hleft : ∀ z ∈ Complex.re ⁻¹' {l}, ‖F z‖ ≤ (12 * C' + 27 + 12 * t₁) * |t₀| ^ κ := by
    intro z hz
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hz
    have hz1 : 1 / 4 ≤ z.re := by rw [hz]; linarith
    have hz2 : z.re ≤ 3 / 4 := by rw [hz]; linarith
    by_cases hs : t₁ ≤ |z.im|
    · set s : ℝ := z.im with hsdef
      have hs1 : 1 ≤ |s| := by linarith
      set w : ℂ := (u : ℂ) - s * I with hw
      have hw_re : w.re = u := by simp [hw]
      have hwz : 1 - w = z := by
        apply Complex.ext
        · simp only [sub_re, one_re, hw_re, hz, hu, hl]; ring
        · simp [hw, hsdef]
      have hwn : ∀ n : ℕ, w ≠ -n := by
        intro n h
        have h' := congrArg Complex.re h
        rw [hw_re] at h'
        simp only [neg_re, natCast_re] at h'
        linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
      have hw1 : w ≠ 1 := by
        intro h
        have h' := congrArg Complex.re h
        rw [hw_re, one_re] at h'
        linarith
      have hfe := riemannZeta_one_sub hwn hw1
      rw [hwz] at hfe
      have h2pi : ‖(2 : ℂ) * (2 * ↑Real.pi) ^ (-w)‖ ≤ 2 := by
        have hbase : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
        rw [norm_mul, hbase, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), neg_re,
          hw_re, Complex.norm_two]
        have : (2 * Real.pi) ^ (-u) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by linarith)
        linarith
      have hΓw : ‖Complex.Gamma w * Complex.cos (↑Real.pi * w / 2)‖ ≤ C' * |s| ^ δ := by
        have h := hΓ (-s) (by rwa [abs_neg])
        rw [abs_neg] at h
        have hw' : w = ((1 / 2 + δ : ℝ) : ℂ) + ((-s : ℝ) : ℂ) * I := by
          rw [hw, hu]; push_cast; ring
        rw [hw']
        exact h.trans (by gcongr; exact le_max_left _ _)
      have hζw : ‖riemannZeta w‖ ≤ |s| ^ ε := by
        have hconj : (starRingEnd ℂ) w = (u : ℂ) + s * I := by
          rw [hw, map_sub, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
          ring
        have h := hR u s le_rfl (by linarith) hs
        rwa [← hconj, riemannZeta_conj, Complex.norm_conj] at h
      have hζz : ‖riemannZeta z‖ ≤ 2 * C' * |s| ^ κ := by
        rw [hfe, show (2 : ℂ) * (2 * ↑Real.pi) ^ (-w) * Complex.Gamma w *
            Complex.cos (↑Real.pi * w / 2) * riemannZeta w =
            ((2 : ℂ) * (2 * ↑Real.pi) ^ (-w)) *
              (Complex.Gamma w * Complex.cos (↑Real.pi * w / 2)) * riemannZeta w by ring,
          norm_mul, norm_mul]
        calc ‖(2 : ℂ) * (2 * ↑Real.pi) ^ (-w)‖ *
              ‖Complex.Gamma w * Complex.cos (↑Real.pi * w / 2)‖ * ‖riemannZeta w‖
            ≤ 2 * (C' * |s| ^ δ) * |s| ^ ε := by gcongr
          _ = 2 * C' * |s| ^ κ := by
            rw [hκ, Real.rpow_add (by linarith)]; ring
      rw [hFn]
      calc ‖riemannZeta z‖ * Real.exp (z.re ^ 2 - (s - t₀) ^ 2)
          ≤ (2 * C' * |s| ^ κ) * (3 * Real.exp (-(s - t₀) ^ 2)) := by
            gcongr
            exact hE z (by linarith) hz2
        _ ≤ (2 * C' * (|t₀| ^ κ * (1 + |s - t₀|))) * (3 * Real.exp (-(s - t₀) ^ 2)) := by
            gcongr
            exact abs_rpow_le ht₀1 hκ0 hδε
        _ = 6 * C' * |t₀| ^ κ * ((1 + |s - t₀|) * Real.exp (-(s - t₀) ^ 2)) := by ring
        _ ≤ 6 * C' * |t₀| ^ κ * 2 := by gcongr; exact one_add_abs_mul_exp_neg_sq_le _
        _ ≤ (12 * C' + 27 + 12 * t₁) * |t₀| ^ κ := by nlinarith
    · push Not at hs
      exact (hsmall z hz1 hz2 hs).trans (by gcongr; linarith)
  -- three lines on the strip `l ≤ re ≤ u`
  have hlu : l < u := by linarith
  have hclosure : closure (HadamardThreeLines.verticalStrip l u) =
      HadamardThreeLines.verticalClosedStrip l u := by
    simp only [HadamardThreeLines.verticalStrip, HadamardThreeLines.verticalClosedStrip,
      closure_preimage_re, closure_Ioo hlu.ne]
  have hd : DiffContOnCl ℂ F (HadamardThreeLines.verticalStrip l u) := by
    apply DifferentiableOn.diffContOnCl
    rw [hclosure]
    intro z hz
    have hz1 : z ≠ 1 := by
      intro h
      have := hz.2
      rw [h, one_re] at this
      linarith
    exact ((differentiableAt_riemannZeta hz1).mul
      (by fun_prop : DifferentiableAt ℂ (fun z => Complex.exp ((z - t₀ * I) ^ 2)) z)
      ).differentiableWithinAt
  have hB : BddAbove ((norm ∘ F) '' HadamardThreeLines.verticalClosedStrip l u) := by
    refine ⟨6 * (9 + 4 * |t₀|), ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have hz1 : 1 / 4 ≤ z.re := by have := hz.1; linarith
    have hz2 : z.re ≤ 3 / 4 := by have := hz.2; linarith
    simp only [Function.comp, hFn]
    have hζ := norm_riemannZeta_le_strip hz1 hz2
    have hpoly : 9 + 4 * |z.im| ≤ (9 + 4 * |t₀|) * (1 + |z.im - t₀|) := by
      have := abs_sub_abs_le_abs_sub z.im t₀
      nlinarith [abs_nonneg (z.im - t₀), abs_nonneg t₀]
    calc ‖riemannZeta z‖ * Real.exp (z.re ^ 2 - (z.im - t₀) ^ 2)
        ≤ ((9 + 4 * |t₀|) * (1 + |z.im - t₀|)) * (3 * Real.exp (-(z.im - t₀) ^ 2)) := by
          gcongr
          · exact hζ.trans hpoly
          · exact hE z (by linarith) hz2
      _ = 3 * (9 + 4 * |t₀|) * ((1 + |z.im - t₀|) * Real.exp (-(z.im - t₀) ^ 2)) := by ring
      _ ≤ 3 * (9 + 4 * |t₀|) * 2 := by gcongr; exact one_add_abs_mul_exp_neg_sq_le _
      _ = 6 * (9 + 4 * |t₀|) := by ring
  set z₀ : ℂ := σ + t₀ * I with hz₀def
  have hz₀re : z₀.re = σ := by simp [hz₀def]
  have hz₀im : z₀.im = t₀ := by simp [hz₀def]
  have hz₀ : z₀ ∈ HadamardThreeLines.verticalClosedStrip l u := by
    simp only [HadamardThreeLines.verticalClosedStrip, Set.mem_preimage, Set.mem_Icc, hz₀re]
    exact ⟨hσl, hσu⟩
  have key := HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip' hlu hz₀ hd hB
    hleft hright
  have hθ0 : 0 ≤ (z₀.re - l) / (u - l) := div_nonneg (by rw [hz₀re]; linarith) (by linarith)
  have hθ1 : (z₀.re - l) / (u - l) ≤ 1 := by
    rw [div_le_one (by linarith), hz₀re]; linarith
  have hmax := rpow_mul_rpow_le_max (by positivity) (by positivity) hθ0 hθ1
    (x := (12 * C' + 27 + 12 * t₁) * |t₀| ^ κ) (y := (33 + 12 * t₁) * |t₀| ^ κ)
  have hFz₀ : ‖riemannZeta z₀‖ ≤ ‖F z₀‖ := by
    rw [hFn, hz₀im, sub_self]
    have : 1 ≤ Real.exp (z₀.re ^ 2 - 0 ^ 2) := Real.one_le_exp (by nlinarith)
    nlinarith [norm_nonneg (riemannZeta z₀)]
  calc ‖riemannZeta z₀‖ ≤ ‖F z₀‖ := hFz₀
    _ ≤ _ := key
    _ ≤ _ := hmax
    _ ≤ (12 * C' + 33 + 12 * t₁) * |t₀| ^ κ := by
      apply max_le
      · gcongr; linarith
      · gcongr; linarith

end Lindelof

end zeta_le_rpow_of_riemannHypothesis

open zeta_le_rpow_of_riemannHypothesis in
/-- **Lindelöf bound from the Riemann hypothesis.** Assume the Riemann hypothesis, and let
$\varepsilon > 0$ be real. Then there are real constants $C$ and $t_0$ such that
$|\zeta(\sigma + it)| \le C |t|^{\varepsilon}$ for all real $\sigma$ and $t$ with
$1/2 \le \sigma \le 1$ and $|t| \ge t_0$.

Source: Kampamolla Venkatasubbareddy and Ayyadurai Sankaranarayanan, *On the
Distribution of the Restricted Sequence of Integers 2^{ω(n)}*, INTEGERS 24
(2024), Article A110, Lemma 8 (`integers-2024-A110-lem-8`). -/
public theorem zeta_le_rpow_of_riemannHypothesis (hRH : RiemannHypothesis)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C t₀ : ℝ, ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → t₀ ≤ |t| →
      ‖riemannZeta (σ + t * I)‖ ≤ C * |t| ^ ε := by
  set ε₀ : ℝ := min ε (1 / 2) with hε₀
  have hε₀pos : 0 < ε₀ := lt_min hε (by norm_num)
  have hε₀le : ε₀ ≤ ε := min_le_left _ _
  have hε₀half : ε₀ ≤ 1 / 2 := min_le_right _ _
  obtain ⟨C, t₂, ht₂, hC⟩ := lindelof_critical hRH (δ := ε₀ / 2) (ε := ε₀ / 2)
    (by linarith) (by linarith) (by linarith) (by linarith)
  obtain ⟨t₁, ht₁, hR⟩ := lindelof_right hRH (δ := ε₀ / 2) (by linarith) (by linarith)
    hε₀pos
  refine ⟨max C 1, max t₁ t₂, ?_⟩
  intro σ t hσ1 hσ2 ht
  have ht1 : 1 ≤ |t| := ht₂.trans ((le_max_right _ _).trans ht)
  have hpow : |t| ^ ε₀ ≤ |t| ^ ε := Real.rpow_le_rpow_of_exponent_le ht1 hε₀le
  have hpos : 0 ≤ |t| ^ ε₀ := by positivity
  have hmax0 : 0 ≤ max C 1 := le_trans zero_le_one (le_max_right _ _)
  by_cases hσ : σ ≤ 1 / 2 + ε₀ / 2
  · have h := hC σ t (by linarith) hσ ((le_max_right _ _).trans ht)
    rw [show ε₀ / 2 + ε₀ / 2 = ε₀ by ring] at h
    exact h.trans (mul_le_mul (le_max_left _ _) hpow hpos hmax0)
  · push Not at hσ
    have h := hR σ t hσ.le hσ2 ((le_max_left _ _).trans ht)
    calc ‖riemannZeta (σ + t * I)‖ ≤ |t| ^ ε₀ := h
      _ ≤ 1 * |t| ^ ε := by rw [one_mul]; exact hpow
      _ ≤ max C 1 * |t| ^ ε := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

end MetaMathlibExt
