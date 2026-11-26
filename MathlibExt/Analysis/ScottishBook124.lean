/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.ContinuousOn

import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import MathlibExt.Analysis.Fourier.FourierLaplace

/-!
# The Volterra form of Scottish Book Problem 124

The Volterra convolution with a continuous kernel nonzero at the origin determines an
integrable function on the unit interval.

For each endpoint `b`, consider the entire transform
$F_b(z) = \int_0^b y(t)e^{(b-t)z}\,dt$. The vanishing convolution bounds its product
with the normalized Laplace transform of the kernel on the positive real axis. The latter
tends to $f(0) \ne 0$. Phragmén–Lindelöf extends the bound on $F_b$ to the right half-plane,
and the integral is bounded directly on the left. Liouville's theorem makes $F_b$ constant.
Its limit at negative infinity is zero, so $F_b(0) = \int_0^b y(t)\,dt = 0$ for every `b`.
Lebesgue differentiation then gives the almost-everywhere conclusion.
-/

@[expose] public section

namespace MathlibExt.Analysis.ScottishBook124Wanted

/-- **The Volterra-form sub-conjecture of Scottish Book Problem 124.** The statement that for every
continuous function $f : \mathbb{R} \to \mathbb{R}$ with $f(0) \ne 0$ and every function
$y : \mathbb{R} \to \mathbb{R}$ that is Lebesgue integrable on $[0, 1]$, if
$\int_0^x y(t) f(x - t)\,dt = 0$ for every $x \in [0, 1]$, then $y = 0$ almost everywhere on
$[0, 1]$.

The Scottish Book typescript prints the upper limit of the integral as $1$, but the entry's own
arguments show that the intended upper limit is $x$ (Volterra form); with upper limit $1$ the
claim is false, since $f \equiv 1$ and $y(t) = t - 1/2$ give a nonzero solution. The typescript
does not specify a function class for $y$; integrability on $[0, 1]$ is motivated by the $L^2$
context of the entry. -/
def ScottishBookProblem124Claim : Prop :=
  ∀ (f : ℝ → ℝ), Continuous f → f 0 ≠ 0 →
    ∀ (y : ℝ → ℝ),
      MeasureTheory.IntegrableOn y (Set.Icc (0 : ℝ) 1) MeasureTheory.volume →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, ∫ t in (0 : ℝ)..x, y t * f (x - t) = 0) →
      y =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)] 0

open Filter Set MeasureTheory
open scoped Topology

/-- The Laplace transform on the interval ending at `b`, translated to put that endpoint at zero. -/
private noncomputable def transform (y : ℝ → ℝ) (b : ℝ) (z : ℂ) : ℂ :=
  ∫ t in Ioc 0 b, (y t : ℂ) * Complex.exp ((b - t : ℝ) * z)

private theorem transform_real (y : ℝ → ℝ) (b s : ℝ) :
    transform y b s = ↑(∫ t in Ioc 0 b, y t * Real.exp ((b - t) * s)) := by
  simp only [transform, ← integral_complex_ofReal, Complex.ofReal_mul, Complex.ofReal_exp]

-- The compactly supported Fourier–Laplace transform is entire. Change its normalization
-- and translate the endpoint to obtain the transform used here.
private theorem transform_differentiable {y : ℝ → ℝ} {b : ℝ}
    (hy : IntegrableOn y (Ioc 0 b)) : Differentiable ℂ (transform y b) := by
  let g := (Ioc 0 b).indicator (fun t => (y t : ℂ))
  have hg : Integrable g := (integrable_indicator_iff measurableSet_Ioc).mpr hy.ofReal
  have hsupp : HasCompactSupport g := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := 0) (b := b))
    exact (support_indicator_subset ..).trans Ioc_subset_Icc_self
  let c : ℂ := -2 * (Real.pi : ℂ) * Complex.I
  have hc : c ≠ 0 := mul_ne_zero
    (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have heq : transform y b = fun z => Complex.exp (b * z) * Fourier.fourierLaplace g (-z / c) := by
    funext z
    rw [transform, ← integral_indicator measurableSet_Ioc, Fourier.fourierLaplace,
      ← integral_const_mul]
    congr 1 with t
    by_cases ht : t ∈ Ioc 0 b
    · simp only [g, indicator_of_mem ht]
      change _ = Complex.exp (b * z) * ((y t : ℂ) * Complex.exp (c * t * (-z / c)))
      rw [mul_left_comm, ← Complex.exp_add, Complex.ofReal_sub]
      congr 2
      field_simp [hc]
      ring
    · simp [g, ht]
  rw [heq]
  exact ((differentiable_id.const_mul (b : ℂ)).cexp).mul
    ((Fourier.differentiable_fourierLaplace hg hsupp).comp (differentiable_id.neg.div_const c))

private theorem transform_norm_le {y : ℝ → ℝ} {b : ℝ} (hy : IntegrableOn y (Ioc 0 b))
    (z : ℂ) (c : ℝ) (hc : ∀ t ∈ Ioc 0 b, (b - t) * z.re ≤ c) :
    ‖transform y b z‖ ≤ (∫ t in Ioc 0 b, ‖y t‖) * Real.exp c := by
  rw [← integral_mul_const]
  apply norm_integral_le_of_norm_le (hy.norm.mul_const _)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  simp only [norm_mul, Complex.norm_real, Complex.norm_exp, Complex.re_ofReal_mul]
  gcongr
  exact hc t ht

-- Boundedness on the positive real axis forces the entire transform to be constant.
private theorem integral_eq_zero_of_bounded_transform {y : ℝ → ℝ} {b : ℝ} (hb : b ≤ 1)
    (hy : IntegrableOn y (Ioc 0 b))
    (hbound : IsBoundedUnder (· ≤ ·) atTop fun s : ℝ => ‖transform y b s‖) :
    ∫ t in Ioc 0 b, y t = 0 := by
  let C := ∫ t in Ioc 0 b, ‖y t‖
  have hd := transform_differentiable hy
  have hleft (z : ℂ) (hz : z.re ≤ 0) : ‖transform y b z‖ ≤ C := by
    simpa [C] using transform_norm_le hy z 0 fun t ht =>
      mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht.2) hz
  have hbounded : Bornology.IsBounded (range (transform y b)) := by
    refine isBounded_iff_forall_norm_le.mpr ⟨C, ?_⟩
    rintro _ ⟨z, rfl⟩
    rcases le_total z.re 0 with hz | hz
    · exact hleft z hz
    refine PhragmenLindelof.right_half_plane_of_bounded_on_real hd.diffContOnCl
      ⟨1, one_lt_two, 1, Asymptotics.IsBigO.of_bound C (.of_forall fun w => ?_)⟩ hbound
      (fun r => hleft _ (by simp)) hz
    simp only [Real.rpow_one, one_mul, Real.norm_eq_abs, Real.abs_exp]
    apply transform_norm_le hy
    intro t ht
    calc
      (b - t) * w.re ≤ (b - t) * ‖w‖ :=
        mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (sub_nonneg.mpr ht.2)
      _ ≤ ‖w‖ := mul_le_of_le_one_left (norm_nonneg _) (by linarith [ht.1])
  -- Along the negative real axis the integrand tends to zero away from the right endpoint.
  have hlim : Tendsto (fun s : ℝ => ∫ t in Ioc 0 b, y t * Real.exp ((b - t) * s))
      atBot (𝓝 0) := by
    convert tendsto_integral_filter_of_dominated_convergence (l := atBot)
      (F := fun (s t : ℝ) => y t * Real.exp ((b - t) * s)) (f := fun _ => 0)
      (fun t => ‖y t‖) (.of_forall fun s => hy.aestronglyMeasurable.mul (by fun_prop)) ?_ hy.norm
      ?_ using 1
    · simp
    · filter_upwards [eventually_le_atBot (0 : ℝ)] with s hs
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      simp only [norm_mul, Real.norm_eq_abs, Real.abs_exp]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht.2) hs))
    · have hne : ∀ᵐ t : ℝ ∂volume.restrict (Ioc 0 b), t ≠ b :=
        ae_restrict_of_ae (by simp [ae_iff])
      filter_upwards [ae_restrict_mem measurableSet_Ioc, hne] with t ht htb
      have hpos := sub_pos.mpr (lt_of_le_of_ne ht.2 htb)
      simpa using (Real.tendsto_exp_atBot.comp
        (tendsto_const_nhds.pos_mul_atBot hpos tendsto_id)).const_mul (y t)
  have hconst (s : ℝ) :
      (∫ t in Ioc 0 b, y t * Real.exp ((b - t) * s)) = ∫ t in Ioc 0 b, y t := by
    have := hd.apply_eq_apply_of_bounded hbounded (s : ℂ) (0 : ℝ)
    rw [transform_real, transform_real y b 0] at this
    simpa using this
  exact tendsto_nhds_unique tendsto_const_nhds (hlim.congr hconst)

-- After dilation the normalized Laplace kernel has density exp(-u) on the positive half-line.
private theorem kernel_limit {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) :
    Tendsto (fun s : ℝ => s * ∫ t in Ioi 0, Real.exp (-s * t) * f t) atTop (𝓝 (f 0)) := by
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioi 0))
    (F := fun (s u : ℝ) => Real.exp (-u) * f (u / s)) (f := fun u => Real.exp (-u) * f 0)
    (fun u => Real.exp (-u) * M) (l := atTop)
    (.of_forall fun s => (by fun_prop)) (by
      exact .of_forall fun s => .of_forall fun u => by
        rw [norm_mul, Real.norm_eq_abs, Real.abs_exp]
        exact mul_le_mul_of_nonneg_left (hM _) (Real.exp_pos _).le)
    ((integrableOn_exp_neg_Ioi 0).mul_const M) (by
      exact .of_forall fun u => tendsto_const_nhds.mul <|
        (hf.tendsto 0).comp (tendsto_const_nhds.div_atTop tendsto_id))
  rw [integral_mul_const, integral_exp_neg_Ioi_zero, one_mul] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  have he := integral_comp_mul_left_Ioi' (fun u => Real.exp (-u) * f (u / s)) 0 hs
  simpa [smul_eq_mul, hs.ne'] using he.symm

private theorem convolution_bound {Y f : ℝ → ℝ} (hY : Integrable Y)
    {M : ℝ} (hM : ∀ t, ‖f t‖ ≤ M) {x : ℝ} (hx : 0 ≤ x) :
    ‖∫ t in 0..x, Y t * f (x - t)‖ ≤ (∫ t, ‖Y t‖) * M := by
  rw [intervalIntegral.integral_of_le hx, ← integral_mul_const]
  refine (norm_integral_le_of_norm_le (hY.norm.mul_const M).integrableOn ?_).trans
    (setIntegral_le_integral (hY.norm.mul_const M) ?_)
  · exact .of_forall fun t => (norm_mul _ _).trans_le <|
      mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
  · exact .of_forall fun t => mul_nonneg (norm_nonneg _) ((norm_nonneg _).trans (hM 0))

-- The unweighted convolution is zero up to b and uniformly bounded beyond b.
-- Its normalized Laplace integral is therefore bounded after translation by b.
private theorem weighted_product_bound {y f : ℝ → ℝ} {b M : ℝ} (hb : 0 ≤ b)
    (hy : IntegrableOn y (Ioc 0 b)) (hf : Continuous f) (hM : ∀ t, ‖f t‖ ≤ M)
    (hzero : ∀ x ∈ Ioc 0 b, ∫ t in 0..x, y t * f (x - t) = 0) {s : ℝ} (hs : 0 < s) :
    ‖(∫ t in Ioc 0 b, y t * Real.exp ((b - t) * s)) *
      (s * ∫ t in Ioi 0, Real.exp (-s * t) * f t)‖ ≤
        (∫ t, ‖(Ioc 0 b).indicator y t‖) * M := by
  let Y := (Ioc 0 b).indicator y
  let U := (Ioc 0 b).indicator (fun t => y t * Real.exp ((b - t) * s))
  let V (t : ℝ) := Real.exp (-s * t) * f t
  let K (x : ℝ) := ∫ t in 0..x, Y t * f (x - t)
  let C := (∫ t, ‖Y t‖) * M
  have hU : Integrable U := (hy.mul_continuousOn_of_subset
    (g' := fun t => Real.exp ((b - t) * s)) (K := Icc 0 b) (by fun_prop)
    measurableSet_Ioc isCompact_Icc Ioc_subset_Icc_self).integrable_indicator measurableSet_Ioc
  have hV : IntegrableOn V (Ioi 0) :=
    ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0).mul_const M).mono' (by dsimp [V]; fun_prop)
      (.of_forall fun t => by
        simp only [V, norm_mul, Real.norm_eq_abs, Real.abs_exp]
        gcongr
        exact hM t)
  have hfactor (x : ℝ) :
      (∫ t in 0..x, U t * V (x - t)) = Real.exp ((b - x) * s) * K x := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1 with t
    dsimp only [U, V, Y]
    rw [indicator_mul_left]
    calc
      _ = (Ioc 0 b).indicator y t * f (x - t) *
          (Real.exp ((b - t) * s) * Real.exp (-s * (x - t))) := by ring
      _ = _ := by rw [← Real.exp_add, show (b - t) * s + -s * (x - t) = (b - x) * s by ring]; ring
  have hK (x : ℝ) (hx : x ∈ Ioc 0 b) : K x = 0 := by
    dsimp only [K]
    apply Eq.trans _ (hzero x hx)
    simp only [intervalIntegral.integral_of_le hx.1.le]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    simp [Y, indicator_of_mem (show t ∈ Ioc 0 b from ⟨ht.1, ht.2.trans hx.2⟩)]
  have hprod := integral_posConvolution hU.integrableOn hV (ContinuousLinearMap.mul ℝ ℝ)
  change (∫ x in Ioi 0, ∫ t in 0..x, U t * V (x - t)) =
    (∫ t in Ioi 0, U t) * ∫ t in Ioi 0, V t at hprod
  simp_rw [hfactor] at hprod
  rw [show (∫ t in Ioi 0, U t) = ∫ t in Ioc 0 b, y t * Real.exp ((b - t) * s) by
    simp only [U, setIntegral_indicator measurableSet_Ioc, inter_eq_right.mpr Ioc_subset_Ioi_self]]
    at hprod
  have htail : (∫ x in Ioi 0, Real.exp ((b - x) * s) * K x) =
      ∫ x in Ioi b, Real.exp ((b - x) * s) * K x := by
    trans ∫ x in Ioi 0, (Ioi b).indicator (fun u => Real.exp ((b - u) * s) * K u) x
    · apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      by_cases h : x ∈ Ioi b
      · simp [indicator_of_mem h]
      · simp [indicator_of_notMem h, hK x ⟨hx, le_of_not_gt h⟩]
    · rw [setIntegral_indicator measurableSet_Ioi, inter_eq_right.mpr (Ioi_subset_Ioi hb)]
  have hexp (x : ℝ) : Real.exp ((b - x) * s) = Real.exp (b * s) * Real.exp (-s * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hdom : IntegrableOn (fun x => Real.exp ((b - x) * s) * C) (Ioi b) := by
    simp_rw [hexp]
    exact ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) b).const_mul _).mul_const _
  have htailBound : ‖∫ x in Ioi b, Real.exp ((b - x) * s) * K x‖ ≤ C / s := calc
    _ ≤ ∫ x in Ioi b, Real.exp ((b - x) * s) * C := by
      apply norm_integral_le_of_norm_le hdom
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      simp only [norm_mul, Real.norm_eq_abs, Real.abs_exp]
      gcongr
      exact convolution_bound (hy.integrable_indicator measurableSet_Ioc) hM (hb.trans hx.le)
    _ = C / s := by
      simp_rw [hexp]
      rw [integral_mul_const, integral_const_mul, integral_exp_mul_Ioi (neg_lt_zero.mpr hs)]
      rw [neg_div_neg_eq, ← mul_div_assoc, ← Real.exp_add, show b * s + -s * b = 0 by ring]
      simp [div_eq_inv_mul]
  change ‖_ * (s * ∫ t in Ioi 0, V t)‖ ≤ C
  rw [mul_left_comm, ← hprod, htail, norm_mul, Real.norm_of_nonneg hs.le]
  exact (le_div_iff₀' hs).mp htailBound

private theorem primitive_eq_zero {y f : ℝ → ℝ} {b : ℝ} (hb : b ∈ Icc 0 1)
    (hy : IntegrableOn y (Ioc 0 b)) (hf : Continuous f) (hf0 : f 0 ≠ 0)
    (hzero : ∀ x ∈ Icc 0 b, ∫ t in 0..x, y t * f (x - t) = 0) :
    ∫ t in 0..b, y t = 0 := by
  -- Extend the restriction of the kernel to the unit interval as a bounded continuous function.
  let g (t : ℝ) := f (max 0 (min 1 t))
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hagree {t : ℝ} (ht : t ∈ Icc 0 1) : g t = f t := by
    simp [g, min_eq_right ht.2, max_eq_right ht.1]
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hf.continuousOn : ContinuousOn f (Icc 0 1))
  have hMg (t : ℝ) : ‖g t‖ ≤ M := hM _ ⟨le_max_left ..,
    max_le zero_le_one (min_le_left ..)⟩
  have hgz (x : ℝ) (hx : x ∈ Ioc 0 b) : ∫ t in 0..x, y t * g (x - t) = 0 := by
    apply Eq.trans _ (hzero x ⟨hx.1.le, hx.2⟩)
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hx.1.le] at ht
    exact congrArg (y t * ·) (hagree ⟨sub_nonneg.mpr ht.2, by linarith [ht.1, hx.2, hb.2]⟩)
  rw [intervalIntegral.integral_of_le hb.1]
  apply integral_eq_zero_of_bounded_transform hb.2 hy
  let c := ‖g 0‖ / 2
  have hc : 0 < c := by simpa [c, g] using half_pos (norm_pos_iff.mpr hf0)
  have hlow := (kernel_limit hg hMg).norm.eventually_const_le (show c < ‖g 0‖ by
    simpa [c, g] using half_lt_self (norm_pos_iff.mpr hf0))
  refine ⟨((∫ t, ‖(Ioc 0 b).indicator y t‖) * M) / c, ?_⟩
  apply eventually_map.mpr
  filter_upwards [hlow, eventually_gt_atTop (0 : ℝ)] with s hs hs0
  rw [transform_real, Complex.norm_real, le_div_iff₀ hc]
  have h := weighted_product_bound hb.1 hy hg hMg hgz hs0
  rw [norm_mul] at h
  exact le_trans (mul_le_mul_of_nonneg_left hs (norm_nonneg _)) h

/--
**The Volterra-form sub-conjecture of Scottish Book Problem 124 holds.** For every continuous
function $f : \mathbb{R} \to \mathbb{R}$ with $f(0) \ne 0$ and every function
$y : \mathbb{R} \to \mathbb{R}$ that is Lebesgue integrable on $[0, 1]$, if
$\int_0^x y(t) f(x - t)\,dt = 0$ for every $x \in [0, 1]$, then $y = 0$ almost everywhere on
$[0, 1]$.

Source: Józef Marcinkiewicz, Problem 124 of the Scottish Book;
typescript PDF p.58, printed p.55.
TYPESCRIPT TYPO, CORRECTED (Phase 5): the typescript prints the
equation as `∫₀¹ y(t) f(x-t) dt = 0`, but the intended upper limit
is `x` (Volterra form). The literal `∫₀¹` reading is false: `f ≡ 1`,
`y(t) = t - 1/2` is a nonzero solution. Only the Volterra `∫₀ˣ`
reading is filed here.
Positive by the local Titchmarsh convolution theorem: E. C.
Titchmarsh, "The zeros of certain integral functions", Proc. London
Math. Soc. s2-25 (1926), 283–302, DOI 10.1112/plms/s2-25.1.283.
Sketch: Titchmarsh gives `λ, μ ≥ 0` with `λ + μ ≥ 1` such that
`y = 0` a.e. on `(0, λ)` and `f = 0` a.e. on `(0, μ)`. Continuity
of `f` at `0` with `f 0 ≠ 0` forces `μ = 0` (otherwise `f` would be
a.e. zero on a positive-measure initial interval while being nonzero
near `0`), so `λ ≥ 1` and `y = 0` a.e. on `[0, 1]`.
-/
theorem marcinkiewicz124_holds : ScottishBookProblem124Claim := by
  intro f hf hf0 y hy hzero
  have hprim (b : ℝ) (hb : b ∈ Icc 0 1) : ∫ t in 0..b, y t = 0 :=
    primitive_eq_zero hb (hy.mono_set fun _ ht => ⟨ht.1.le, ht.2.trans hb.2⟩) hf hf0
      fun x hx => hzero x ⟨hx.1, hx.2.trans hb.2⟩
  have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr hy
  have hd := hi.ae_hasDerivAt_integral
  rw [uIcc_of_le zero_le_one] at hd
  apply (ae_restrict_iff' measurableSet_Icc).mpr
  filter_upwards [hd] with x hx hxI
  have hderiv := (hx hxI 0 ⟨le_rfl, zero_le_one⟩).hasDerivWithinAt
    (s := Icc (0 : ℝ) 1)
  have hconst : HasDerivWithinAt (fun _ : ℝ => (0 : ℝ)) (y x) (Icc 0 1) x :=
    hderiv.congr (fun t ht => (hprim t ht).symm) (hprim x hxI).symm
  simpa using (hconst.derivWithin (uniqueDiffOn_Icc_zero_one x hxI)).symm

end MathlibExt.Analysis.ScottishBook124Wanted
