/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Algebra.BigOperators.Group.Finset.Interval
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Algebra.Ring.Periodic
import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.Convex.Slope
import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue
import MathlibExt.Analysis.Fourier.Fejer
import MathlibExt.Analysis.SineIntegral

/-!
# The Dirichlet–Jordan theorem

The symmetric Fourier sums of a periodic function of bounded variation converge at each point
to the average of its one-sided limits.

On each half of a period centered at the evaluation point, factor the Dirichlet kernel into
a scaled sinc and the reciprocal of `sinc (t / 2)`. The latter factor has bounded variation.
Jordan decomposition reduces the resulting estimate to monotone real weights. For these weights,
the second mean value theorem reduces the integral on each subinterval to a difference of sine
integrals.
-/

open MeasureTheory Complex Set Filter Topology
open scoped ENNReal ComplexConjugate Real BigOperators

namespace MathlibExt.Analysis.Fourier.DirichletTheoremWanted

open MathlibExt.Analysis.SineIntegral

private noncomputable def kernel (s t : ℝ) := s * Real.sinc (t * s)

private lemma kernel_continuous (s : ℝ) : Continuous (kernel s) :=
  continuous_const.mul (Real.continuous_sinc.comp (continuous_id.mul continuous_const))

private lemma integral_kernel (s a b : ℝ) :
    ∫ t in a..b, kernel s t = sineIntegral (s * b) - sineIntegral (s * a) := by
  rw [← integral_mul_sinc, ← integral_mul_sinc]
  exact eq_sub_of_add_eq' (intervalIntegral.integral_add_adjacent_intervals
    ((kernel_continuous s).intervalIntegrable 0 a) ((kernel_continuous s).intervalIntegrable a b))

private lemma right_limit {E : Type*} [MetricSpace E] [CompleteSpace E]
    {g : ℝ → E} {b : ℝ} (hb : 0 < b) (hg : BoundedVariationOn g (Icc 0 b)) :
    ∃ l, Tendsto g (𝓝[>] 0) (𝓝 l) := by
  obtain ⟨l, hl⟩ := hg.exists_tendsto_right 0
  refine ⟨l, hl.mono_left ?_⟩
  rw [nhdsWithin_inter]
  refine le_inf (le_inf nhdsWithin_le_nhds ?_) le_rfl
  exact le_principal_iff.mpr (mem_of_superset ((nhdsGT_basis_Ioc 0).mem_of_mem hb)
    Ioc_subset_Icc_self)

private lemma monotone_bv {g : ℝ → ℝ} {a b : ℝ} (hg : MonotoneOn g (Icc a b)) :
    BoundedVariationOn g (Icc a b) := by
  apply hg.boundedVariationOn (C := |g a| + |g b|)
  intro x hx
  have h := hg.mapsTo_Icc hx
  exact abs_le.mpr ⟨by linarith [h.1, neg_abs_le (g a), abs_nonneg (g b)],
    by linarith [h.2, le_abs_self (g b), abs_nonneg (g a)]⟩

private lemma kernel_tendsto_zero {g : ℝ → ℝ} {b : ℝ} (hb : 0 < b)
    (hg : MonotoneOn g (Icc 0 b)) (hg₀ : 0 ≤ g 0) (hl : Tendsto g (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun s ↦ ∫ t in (0 : ℝ)..b, g t * kernel s t) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hev : ∀ᶠ d in 𝓝[>] (0 : ℝ), d ∈ Ioc 0 b := (nhdsGT_basis_Ioc 0).mem_of_mem hb
  obtain ⟨d, hd, hsmall⟩ := (hev.and
    (hl.eventually_lt_const (show 0 < ε / 16 by positivity))).exists
  have hd₀ := hd.1
  have hdb := hd.2
  have hgd := hg₀.trans (hg ⟨le_rfl, hb.le⟩ ⟨hd₀.le, hdb⟩ hd₀.le)
  -- On the short interval the weight is small and every kernel primitive is bounded.
  have near (s : ℝ) : |∫ t in (0 : ℝ)..d, g t * kernel s t| ≤ g d * 8 := by
    obtain ⟨c, _, hc⟩ := exists_eq_const_mul_intervalIntegral_of_nonneg_of_monotoneOn
      hd₀.le hg₀ (hg.mono (Icc_subset_Icc_right hdb)) ((kernel_continuous s).intervalIntegrable 0 d)
    rw [hc, integral_kernel, abs_mul, abs_of_nonneg hgd]
    gcongr
    linarith [abs_sub (sineIntegral (s * d)) (sineIntegral (s * c)),
      abs_sineIntegral_le (s * d), abs_sineIntegral_le (s * c)]
  -- On the remaining interval both arguments of the sine integral tend to infinity.
  choose c hc he using fun s : ℝ ↦
    exists_eq_const_mul_intervalIntegral_of_nonneg_of_monotoneOn hdb hgd
      (hg.mono (Icc_subset_Icc_left hd₀.le)) ((kernel_continuous s).intervalIntegrable d b)
  have hc_top : Tendsto (fun s ↦ s * c s) atTop atTop := by
    refine tendsto_atTop_mono' _ ?_ (tendsto_id.atTop_mul_const hd₀)
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs using
      mul_le_mul_of_nonneg_left (hc s).1 hs
  have far : Tendsto (fun s ↦ ∫ t in d..b, g t * kernel s t) atTop (𝓝 0) := by
    simp_rw [he, integral_kernel]
    simpa using ((tendsto_sineIntegral_atTop.comp (tendsto_id.atTop_mul_const hb)).sub
      (tendsto_sineIntegral_atTop.comp hc_top)).const_mul (g b)
  filter_upwards [(Metric.tendsto_nhds.mp far (ε / 2) (by positivity))] with s hs
  have hi {u v : ℝ} (huv : u ≤ v) (hu : 0 ≤ u) (hv : v ≤ b) :
      IntervalIntegrable (fun t ↦ g t * kernel s t) volume u v :=
    ((monotone_bv hg).intervalIntegrable (by rw [uIcc_of_le huv]; exact Icc_subset_Icc hu hv)
      ).mul_continuousOn (kernel_continuous s).continuousOn
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hi hd₀.le le_rfl hdb) (hi hdb hd₀.le le_rfl), Real.dist_eq, sub_zero]
  rw [Real.dist_eq, sub_zero] at hs
  exact (abs_add_le _ _).trans_lt (by linarith [near s])

private lemma monotone_kernel_limit {g : ℝ → ℝ} {b : ℝ} (hb : 0 < b)
    (hg : MonotoneOn g (Icc 0 b)) :
    ∃ l, Tendsto g (𝓝[>] 0) (𝓝 l) ∧
      Tendsto (fun s ↦ ∫ t in (0 : ℝ)..b, g t * kernel s t) atTop (𝓝 (l * (π / 2))) := by
  obtain ⟨l, hl⟩ := right_limit hb (monotone_bv hg)
  -- Taking the positive part also handles a jump between the endpoint and its right limit.
  let h (t : ℝ) := max (g t - l) 0
  have hm : MonotoneOn h (Icc 0 b) :=
    fun x hx y hy hxy ↦ max_le_max (sub_le_sub_right (hg hx hy hxy) l) le_rfl
  have hz := kernel_tendsto_zero hb hm (le_max_right _ _) (by
    simpa [h] using (hl.sub_const l).max (tendsto_const_nhds (x := (0 : ℝ))))
  have hconst := (tendsto_sineIntegral_atTop.comp (tendsto_id.atTop_mul_const hb)).const_mul l
  have hsum := hz.add hconst
  rw [zero_add] at hsum
  refine ⟨l, hl, hsum.congr' ?_⟩
  apply Eventually.of_forall
  intro s
  simp only [Function.comp_apply, id_eq]
  rw [← integral_mul_sinc, ← intervalIntegral.integral_const_mul]
  change (∫ t in (0 : ℝ)..b, h t * kernel s t) + (∫ t in (0 : ℝ)..b, l * kernel s t) = _
  rw [← intervalIntegral.integral_add
    (((monotone_bv hm).intervalIntegrable (by rw [uIcc_of_le hb.le])).mul_continuousOn
      (kernel_continuous s).continuousOn)
    (((kernel_continuous s).intervalIntegrable 0 b).const_mul l)]
  apply intervalIntegral.integral_congr_Ioo_of_le hb.le
  intro t ht
  have hlt : l ≤ g t := le_of_tendsto hl (by
    filter_upwards [(nhdsGT_basis_Ioc 0).mem_of_mem ht.1] with y hy using
      hg ⟨hy.1.le, hy.2.trans ht.2.le⟩ ⟨ht.1.le, ht.2.le⟩ hy.2)
  simp only [h, max_eq_left (sub_nonneg.mpr hlt)]
  ring

private lemma bv_kernel_limit {g : ℝ → ℝ} {b l : ℝ} (hb : 0 < b)
    (hg : BoundedVariationOn g (Icc 0 b)) (hl : Tendsto g (𝓝[>] 0) (𝓝 l)) :
    Tendsto (fun s ↦ ∫ t in (0 : ℝ)..b, g t * kernel s t) atTop (𝓝 (l * (π / 2))) := by
  obtain ⟨p, q, hp, hq, rfl⟩ := hg.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn
  obtain ⟨lp, hlp, hip⟩ := monotone_kernel_limit hb hp
  obtain ⟨lq, hlq, hiq⟩ := monotone_kernel_limit hb hq
  have he : l = lp - lq := tendsto_nhds_unique hl (hlp.sub hlq)
  rw [he, sub_mul]
  refine (hip.sub hiq).congr fun s ↦ ?_
  have hi {v : ℝ → ℝ} (hv : MonotoneOn v (Icc 0 b)) :=
    ((monotone_bv hv).intervalIntegrable (μ := volume) (a := 0) (b := b)
      (by rw [uIcc_of_le hb.le])).mul_continuousOn (kernel_continuous s).continuousOn
  simp only [Pi.sub_apply, sub_mul, intervalIntegral.integral_sub (hi hp) (hi hq)]

private noncomputable def weight (t : ℝ) := (Real.sinc (t / 2))⁻¹

private lemma weight_bv : BoundedVariationOn weight (Icc 0 π) := by
  apply monotone_bv
  intro x hx y hy hxy
  have hpos {t : ℝ} (ht : t ∈ Icc 0 π) : 0 < Real.sinc (t / 2) :=
    Real.sinc_pos (by rw [abs_of_nonneg (by linarith [ht.1])]; linarith [ht.2, Real.pi_pos])
  apply (inv_le_inv₀ (hpos hx) (hpos hy)).2
  obtain hx₀ | hx₀ := hx.1.eq_or_lt
  · simp [← hx₀, Real.sinc_le_one]
  have hy₀ := hx₀.trans_le hxy
  rw [Real.sinc_of_ne_zero (by positivity), Real.sinc_of_ne_zero (by positivity)]
  have h := strictConcaveOn_sin_Icc.concaveOn.neg.secant_mono
    (a := 0) (x := x / 2) (y := y / 2) ⟨le_rfl, Real.pi_pos.le⟩
    ⟨by positivity, by linarith [hx.2, Real.pi_pos]⟩
    ⟨by positivity, by linarith [hy.2, Real.pi_pos]⟩ (by positivity) (by positivity) (by linarith)
  simpa [neg_div] using h

private lemma weighted_kernel_limit {g : ℝ → ℂ} {l : ℂ}
    (hg : BoundedVariationOn g (Icc 0 π)) (hl : Tendsto g (𝓝[>] 0) (𝓝 l)) :
    Tendsto (fun s ↦ ∫ t in (0 : ℝ)..π, (kernel s t * weight t) • g t) atTop
      (𝓝 ((π / 2) • l)) := by
  have hw : Tendsto weight (𝓝[>] 0) (𝓝 1) := by
    have h := (Real.continuous_sinc.comp (continuous_id.div_const 2)).continuousAt
      (x := (0 : ℝ))
    unfold weight
    simpa [Function.comp_def, Pi.inv_def] using
      (h.inv₀ (by simp)).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  have hpart (L : ℂ →L[ℝ] ℝ) : Tendsto
      (fun s ↦ L (∫ t in (0 : ℝ)..π, (kernel s t * weight t) • g t))
      atTop (𝓝 (L ((π / 2) • l))) := by
    have hbv := weight_bv.mul (L.lipschitzWith.comp_boundedVariationOn hg)
    have hlim : Tendsto (fun t ↦ weight t * L (g t)) (𝓝[>] 0) (𝓝 (L l)) := by
      simpa using hw.mul (L.continuous.continuousAt.tendsto.comp hl)
    have hk := bv_kernel_limit Real.pi_pos hbv hlim
    rw [map_smul, smul_eq_mul, mul_comm]
    refine hk.congr fun s ↦ ?_
    have hi := (weight_bv.smul hg).intervalIntegrable (μ := volume) (a := 0) (b := π)
      (by rw [uIcc_of_le Real.pi_pos.le])
    have hin : IntervalIntegrable (fun t ↦ (kernel s t * weight t) • g t) volume 0 π := by
      simpa only [← smul_smul, Pi.smul_apply'] using
        hi.continuousOn_smul (kernel_continuous s).continuousOn
    rw [← L.intervalIntegral_comp_comm hin]
    simp only [map_smul, smul_eq_mul, Pi.mul_apply, Function.comp_apply]
    congr 1
    funext t
    ring
  have hre := (hpart reCLM).ofReal
  have him := (hpart imCLM).ofReal.mul_const I
  simpa only [reCLM_apply, imCLM_apply, re_add_im] using hre.add him

private noncomputable def wave (n : ℤ) (t : ℝ) : ℂ := exp (((n : ℂ) * t) * I)

private noncomputable def dirichlet (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), wave n t

private lemma dirichlet_sin (N : ℕ) (t : ℝ) :
    dirichlet N t * (Real.sin (t / 2) : ℂ) = Real.sin (((N : ℝ) + 1 / 2) * t) := by
  induction N with
  | zero => simp [dirichlet, wave, div_eq_inv_mul]
  | succ N ih =>
    have step : dirichlet (N + 1) t =
        ((2 * Real.cos (((N : ℝ) + 1) * t) : ℝ) : ℂ) + dirichlet N t := by
      rw [dirichlet, Nat.cast_add_one, Finset.sum_Icc_succ_eq_add_endpoints]
      congr 1
      simp only [wave, Int.cast_neg, Int.cast_add, Int.cast_one, Int.cast_natCast,
        exp_mul_I, ofReal_mul, ofReal_ofNat, ofReal_cos,
        ofReal_add, ofReal_natCast, ofReal_one]
      rw [neg_mul, cos_neg, sin_neg]
      ring
    rw [step, add_mul, ih, ← ofReal_mul, ← ofReal_add]
    apply congrArg ofReal
    push_cast
    have h := Real.sin_sub_sin (((N : ℝ) + 1 + 1 / 2) * t) (((N : ℝ) + 1 / 2) * t)
    rw [show (((N : ℝ) + 1 + 1 / 2) * t - ((N : ℝ) + 1 / 2) * t) / 2 = t / 2 by
      ring, show (((N : ℝ) + 1 + 1 / 2) * t + ((N : ℝ) + 1 / 2) * t) / 2 =
        ((N : ℝ) + 1) * t by ring] at h
    linarith

private lemma dirichlet_eq_kernel (N : ℕ) {t : ℝ} (ht : t ≠ 0) (hb : |t| ≤ π) :
    dirichlet N t = ((2 * kernel ((N : ℝ) + 1 / 2) t * weight t : ℝ) : ℂ) := by
  let s := (N : ℝ) + 1 / 2
  have hs : 0 < s := by dsimp [s]; positivity
  have hhalf : t / 2 ≠ 0 := div_ne_zero ht two_ne_zero
  have hsin : Real.sin (t / 2) ≠ 0 := by
    have h := Real.sinc_pos (x := t / 2) (by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith [Real.pi_pos])
    rw [Real.sinc_of_ne_zero hhalf] at h
    exact (div_ne_zero_iff.mp h.ne').1
  apply mul_right_cancel₀ (ofReal_ne_zero.mpr hsin)
  rw [dirichlet_sin, ← ofReal_mul]
  apply congrArg ofReal
  change Real.sin (s * t) = 2 * (s * Real.sinc (t * s)) * (Real.sinc (t / 2))⁻¹ * _
  rw [Real.sinc_of_ne_zero (mul_ne_zero ht hs.ne'), Real.sinc_of_ne_zero hhalf, mul_comm t s]
  field_simp

private lemma periodic_bv {f : ℝ → ℂ} (hp : Function.Periodic f (2 * π))
    (hb : BoundedVariationOn f (Icc (-π) π)) (x : ℝ) :
    BoundedVariationOn f (Icc (x - π) (x + π)) := by
  have shift {a b c : ℝ} (he : ∀ y, f (y - c) = f y)
      (hs : BoundedVariationOn f (Icc a b)) {u v : ℝ} (hu : a ≤ u - c) (hv : v - c ≤ b) :
      BoundedVariationOn f (Icc u v) := by
    have h := eVariationOn.comp_le_of_monotoneOn f (fun y ↦ y - c)
      (s := Icc a b) (t := Icc u v) (fun _ _ _ _ h ↦ sub_le_sub_right h c)
      (fun y hy ↦ ⟨by linarith [hy.1], by linarith [hy.2]⟩)
    simpa only [BoundedVariationOn, Function.comp_def, he] using ne_top_of_le_ne_top hs h
  have hb' : BoundedVariationOn f (Icc π (3 * π)) :=
    shift hp.sub_eq hb (by linarith) (by linarith)
  have hu : BoundedVariationOn f (Icc (-π) (3 * π)) := by
    have h := eVariationOn.Icc_add_Icc f (s := univ) (a := -π) (b := π) (c := 3 * π)
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (mem_univ _)
    simp only [univ_inter] at h
    rw [BoundedVariationOn, ← h]
    exact ENNReal.add_ne_top.mpr ⟨hb, hb'⟩
  let k := toIocDiv Real.two_pi_pos (-π) (x - π)
  have hk : x - π - k • (2 * π) ∈ Ioc (-π) (-π + 2 * π) :=
    sub_toIocDiv_zsmul_mem_Ioc Real.two_pi_pos _ _
  exact shift (fun _ ↦ hp.sub_zsmul_eq k) hu hk.1.le (by linarith [hk.2])

private lemma fourier_eq_wave (n : ℤ) (t : ℝ) :
    (fourier n (t : AddCircle (2 * π)) : ℂ) = wave n t := by
  rw [MathlibExt.Analysis.FourierConvergenceWanted.Analysis.fourier_coe_two_pi]
  unfold wave
  congr 1
  ring

private lemma coeff_term {f : ℝ → ℂ} (hp : Function.Periodic f (2 * π)) (n : ℤ) (x : ℝ) :
    fourierCoeffOn Real.two_pi_pos f n * exp (I * n * x) =
      (1 / (2 * π)) • ∫ t in (-π)..π, wave n (-t) * f (x + t) := by
  have hper : Function.Periodic (wave (-n)) (2 * π) := by
    intro t
    rw [← fourier_eq_wave, ← fourier_eq_wave, AddCircle.coe_add, AddCircle.coe_period, add_zero]
  let F (t : ℝ) := wave (-n) t * f t
  have hF : Function.Periodic F (2 * π) := hper.mul hp
  have hshift := hF.intervalIntegral_add_eq 0 (x - π)
  simp only [zero_add, show x - π + 2 * π = x + π by ring] at hshift
  rw [fourierCoeffOn_eq_integral, sub_zero]
  simp only [smul_eq_mul, fourier_eq_wave]
  change ((1 / (2 * π) : ℝ) • (∫ t in (0 : ℝ)..2 * π, F t)) * _ = _
  rw [hshift, smul_mul_assoc, ← intervalIntegral.integral_mul_const]
  congr 1
  have hadd := intervalIntegral.integral_comp_add_left (fun t ↦ F t * exp (I * n * x))
    (a := -π) (b := π) x
  rw [sub_eq_add_neg x π, ← hadd]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [F, wave, Int.cast_neg, ofReal_neg, ofReal_add]
  rw [mul_right_comm, ← exp_add]
  congr 2
  ring

private lemma partial_sum_integral {f : ℝ → ℂ} (hp : Function.Periodic f (2 * π))
    (x : ℝ) (hb : BoundedVariationOn f (Icc (x - π) (x + π))) (N : ℕ) :
    (∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), fourierCoeffOn Real.two_pi_pos f n *
      exp (I * n * x)) = (1 / (2 * π)) • ∫ t in (-π)..π, dirichlet N (-t) * f (x + t) := by
  have hi : IntervalIntegrable (fun t ↦ f (x + t)) volume (-π) π := by
    have h := hb.intervalIntegrable (μ := volume) (a := x - π) (b := x + π)
      (by rw [uIcc_of_le (by linarith [Real.pi_pos])])
    convert h.comp_add_left x using 1 <;> ring
  simp_rw [coeff_term hp, ← Finset.smul_sum]
  congr 1
  simp only [dirichlet, Finset.sum_mul]
  exact (intervalIntegral.integral_finsetSum fun n _ ↦ hi.continuousOn_mul
    (by unfold wave; fun_prop)).symm

private lemma partial_sum_halves {f : ℝ → ℂ} (hp : Function.Periodic f (2 * π)) (x : ℝ)
    (hb : BoundedVariationOn f (Icc (x - π) (x + π))) (N : ℕ) :
    (∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), fourierCoeffOn Real.two_pi_pos f n *
      exp (I * n * x)) =
      (1 / π) • ((∫ t in (0 : ℝ)..π, (kernel (N + 1 / 2) t * weight t) • f (x + t)) +
        ∫ t in (0 : ℝ)..π, (kernel (N + 1 / 2) t * weight t) • f (x - t)) := by
  let F (t : ℝ) := dirichlet N (-t) * f (x + t)
  have hi {a b : ℝ} (hab : a ≤ b) (ha : -π ≤ a) (hb' : b ≤ π) :
      IntervalIntegrable F volume a b := by
    have h := hb.intervalIntegrable (μ := volume) (a := x + a) (b := x + b)
      (by rw [uIcc_of_le (by linarith)]; exact Icc_subset_Icc (by linarith) (by linarith))
    have hh : IntervalIntegrable (fun t ↦ f (x + t)) volume a b := by simpa using h.comp_add_left x
    apply hh.continuousOn_mul
    unfold dirichlet wave
    fun_prop
  have hleft := intervalIntegral.integral_comp_neg (a := 0) (b := π) F
  simp only [neg_zero] at hleft
  have hplus : (∫ t in (0 : ℝ)..π, F t) =
      (2 : ℝ) • ∫ t in (0 : ℝ)..π, (kernel (N + 1 / 2) t * weight t) • f (x + t) := by
    rw [← intervalIntegral.integral_smul]
    apply intervalIntegral.integral_congr_Ioo_of_le Real.pi_pos.le
    intro t ht
    dsimp only [F]
    rw [dirichlet_eq_kernel N (neg_ne_zero.mpr ht.1.ne')
      (by rw [abs_neg, abs_of_pos ht.1]; exact ht.2.le)]
    simp [kernel, weight, neg_mul, neg_div, real_smul, mul_assoc]
  have hminus : (∫ t in (0 : ℝ)..π, F (-t)) =
      (2 : ℝ) • ∫ t in (0 : ℝ)..π, (kernel (N + 1 / 2) t * weight t) • f (x - t) := by
    rw [← intervalIntegral.integral_smul]
    apply intervalIntegral.integral_congr_Ioo_of_le Real.pi_pos.le
    intro t ht
    simp only [F, neg_neg]
    rw [dirichlet_eq_kernel N ht.1.ne' (by rw [abs_of_pos ht.1]; exact ht.2.le)]
    simp [real_smul, sub_eq_add_neg, mul_assoc]
  rw [partial_sum_integral hp x hb]
  change (1 / (2 * π)) • (∫ t in (-π)..π, F t) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hi (neg_nonpos.mpr Real.pi_pos.le) le_rfl Real.pi_pos.le)
    (hi Real.pi_pos.le (neg_nonpos.mpr Real.pi_pos.le) le_rfl), ← hleft, hminus, hplus,
    ← smul_add, smul_smul, add_comm (∫ t in (0 : ℝ)..π, _)]
  congr 1
  field_simp

/-- **Dirichlet–Jordan theorem on pointwise convergence of Fourier series.** Let
$f : \mathbb{R} \to \mathbb{C}$ be $2\pi$-periodic and of bounded variation on $[-\pi, \pi]$,
and for $n \in \mathbb{Z}$ let $c_n = \frac{1}{2\pi} \int_0^{2\pi} f(t) e^{-int}\,dt$ be its
Fourier coefficients. Then at every $x \in \mathbb{R}$ the one-sided limits
$f(x^+) = \lim_{y \to x,\, y > x} f(y)$ and $f(x^-) = \lim_{y \to x,\, y < x} f(y)$ exist, and
the symmetric partial sums of the Fourier series converge to their average:
$$\lim_{N \to \infty} \sum_{n=-N}^{N} c_n e^{inx} = \frac{f(x^+) + f(x^-)}{2}.$$
By periodicity, the coefficients $c_n$ equal the corresponding integrals over $[-\pi, \pi]$.

This is the bounded-variation (Dirichlet–Jordan) form. It is distinct from the version of
Dirichlet's theorem that assumes $f$ continuously differentiable and concludes convergence to
$f(x)$; here $f$ may be discontinuous and the limit is the average of the one-sided limits.

Sources:
- Mathlib `docs/undergrad.yaml`, section "Measures and integral calculus /
  Fourier analysis", entry "Dirichlet theorem" (currently missing: empty entry,
  no Mathlib declaration).
- Y. Katznelson, *An Introduction to Harmonic Analysis*, 3rd ed., Ch. II, §2
  (functions of bounded variation; Dirichlet–Jordan test).
- https://en.wikipedia.org/wiki/Dirichlet%27s_theorem_on_Fourier_series
-/
public theorem dirichlet_pointwise_convergence
    (f : ℝ → ℂ)
    (hf_periodic : Function.Periodic f (2 * Real.pi))
    (hf_bv : BoundedVariationOn f (Icc (-Real.pi) Real.pi)) :
    ∀ x : ℝ, ∃ lPlus lMinus : ℂ,
      Tendsto f (nhdsWithin x (Ioi x)) (nhds lPlus) ∧
      Tendsto f (nhdsWithin x (Iio x)) (nhds lMinus) ∧
      Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          fourierCoeffOn Real.two_pi_pos f n * Complex.exp (Complex.I * (n : ℂ) * (x : ℂ)))
        atTop (nhds ((lPlus + lMinus) / 2)) := by
  intro x
  have hb := periodic_bv hf_periodic hf_bv x
  have hp : BoundedVariationOn (fun t ↦ f (x + t)) (Icc 0 π) :=
    ne_top_of_le_ne_top hb (eVariationOn.comp_le_of_monotoneOn f (fun t ↦ x + t)
      (fun _ _ _ _ h ↦ add_le_add_right h x)
      (fun _ ht ↦ ⟨by linarith [ht.1, Real.pi_pos], by linarith [ht.2]⟩))
  have hm : BoundedVariationOn (fun t ↦ f (x - t)) (Icc 0 π) :=
    ne_top_of_le_ne_top hb (eVariationOn.comp_le_of_antitoneOn f (fun t ↦ x - t)
      (fun _ _ _ _ h ↦ sub_le_sub_left h x)
      (fun _ ht ↦ ⟨by linarith [ht.2], by linarith [ht.1, Real.pi_pos]⟩))
  obtain ⟨lPlus, hPlus⟩ := right_limit Real.pi_pos hp
  obtain ⟨lMinus, hMinus⟩ := right_limit Real.pi_pos hm
  refine ⟨lPlus, lMinus, ?_, ?_, ?_⟩
  · have h : Tendsto (fun y ↦ y - x) (𝓝[>] x) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · simpa using (tendsto_id (x := 𝓝 x)).sub_const x |>.mono_left
          (nhdsWithin_le_nhds (s := Ioi x))
      · filter_upwards [self_mem_nhdsWithin] with y hy using sub_pos.mpr hy
    simpa [Function.comp_def] using hPlus.comp h
  · have h : Tendsto (fun y ↦ x - y) (𝓝[<] x) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · simpa using (tendsto_id (x := 𝓝 x)).const_sub x |>.mono_left
          (nhdsWithin_le_nhds (s := Iio x))
      · filter_upwards [self_mem_nhdsWithin] with y hy using sub_pos.mpr hy
    simpa [Function.comp_def] using hMinus.comp h
  · have hfreq : Tendsto (fun N : ℕ ↦ (N : ℝ) + 1 / 2) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    have h := (((weighted_kernel_limit hp hPlus).add
      (weighted_kernel_limit hm hMinus)).comp hfreq).const_smul (1 / π)
    rw [← smul_add, smul_smul] at h
    have hval (z : ℂ) : (1 / π * (π / 2)) • z = z / 2 := by
      rw [real_smul]
      push_cast
      field_simp [Real.pi_ne_zero]
    rw [hval] at h
    exact h.congr fun N ↦ (partial_sum_halves hf_periodic x hb N).symm

end MathlibExt.Analysis.Fourier.DirichletTheoremWanted
