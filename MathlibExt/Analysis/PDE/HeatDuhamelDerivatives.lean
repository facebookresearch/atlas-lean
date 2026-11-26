/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PDE.HeatDuhamel
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Classical derivatives of heat-kernel Duhamel integrals

Spatial derivatives can be transferred to the forcing when those derivatives
are jointly continuous and have uniform exponential growth on the time strip.
The first-derivative statement assumes only C1 spatial data; time differentiability
of the forcing is not needed. Gaussian moment bounds justify differentiation
under the actual time integral, including at initial time.

For C2 spatial forcing, the time derivative equals the forcing plus the viscosity
times the second spatial derivative on the open time strip. A fixed-interval
representation and a uniform Lipschitz bound justify differentiation despite
the corner in the stationary heat extension. No time derivative of the forcing
is required; no ordinary time derivative at either endpoint is asserted.

This is the spatial derivative-transfer argument in Stanford Math 220B,
*Heat Equation*, §2.7.2, extended by exponential Gaussian domination:
https://web.stanford.edu/class/math220b/handouts/heateqn.pdf.
-/

@[expose] public section

open MeasureTheory Set Real Filter Topology
open MathlibExt.Analysis

namespace MathlibExt.Analysis.PDE.HeatKernel

private theorem slice_cont {f : ℝ → ℝ → ℝ} {T s : ℝ}
    (hf : ContinuousOn (Function.uncurry f) (Icc 0 T ×ˢ univ)) (hs : s ∈ Icc 0 T) :
    Continuous (f s) :=
  hf.comp_continuous (continuous_const.prodMk continuous_id) (fun y => ⟨hs, mem_univ y⟩)

private theorem slice_growth {f : ℝ → ℝ → ℝ} {T s : ℝ}
    (hg : HeatWholeLine.HasExpGrowthOnStrip f T) (hs : s ∈ Icc 0 T) :
    HasExpGrowth (f s) := by
  obtain ⟨M, c, hM, hc, hb⟩ := hg
  exact ⟨M, c, hM, hc, hb s hs⟩

private theorem heat_transfer {f fx : ℝ → ℝ}
    (hfx : Continuous fx) (hgf : HasExpGrowth f) (hgfx : HasExpGrowth fx)
    (hd : ∀ x, HasDerivAt f (fx x) x) (t x : ℝ) :
    HasDerivAt (heatSolution f t) (heatSolution fx t x) x := by
  have he : deriv f = fx := funext (fun x => (hd x).deriv)
  have hc : ContDiff ℝ 1 f := contDiff_one_iff_deriv.mpr
    ⟨fun x => (hd x).differentiableAt, by rw [he]; exact hfx⟩
  simpa only [he] using heatSolution_hasDerivAt_deriv_of_exp_growth hc hgf
    (by rw [he]; exact hgfx) t x

private theorem heat_time_transfer {f fx fxx : ℝ → ℝ}
    (hf : Continuous f) (hfx : Continuous fx) (hfxx : Continuous fxx)
    (hgf : HasExpGrowth f) (hgfx : HasExpGrowth fx) (hgfxx : HasExpGrowth fxx)
    (hd : ∀ x, HasDerivAt f (fx x) x) (hdd : ∀ x, HasDerivAt fx (fxx x) x)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun r => heatSolution f r x) (heatSolution fxx t x) t := by
  have he : deriv (heatSolution f t) = heatSolution fx t :=
    funext (fun x => (heat_transfer hfx hgf hgfx hd t x).deriv)
  simpa only [he, (heat_transfer hfxx hgfx hgfxx hdd t x).deriv] using
    heatSolution_hasDerivAt_time_of_exp_growth hf.aestronglyMeasurable hgf ht x

private theorem heat_time_lipschitz {f fx fxx : ℝ → ℝ}
    (hf : Continuous f) (hfx : Continuous fx) (hfxx : Continuous fxx)
    (hgf : HasExpGrowth f) (hgfx : HasExpGrowth fx) (hgfxx : HasExpGrowth fxx)
    (hd : ∀ x, HasDerivAt f (fx x) x) (hdd : ∀ x, HasDerivAt fx (fxx x) x)
    {H C : ℝ} (hH : 0 < H) (hC : 0 ≤ C) (x : ℝ)
    (hb : ∀ r ∈ Ioo 0 H, |heatSolution fxx r x| ≤ C) :
    LipschitzOnWith (NNReal.mk C hC) (fun r => heatSolution f r x) (Iic H) := by
  have hcont : Continuous (fun r => heatSolution f r x) :=
    (heatSolution_continuous_of_exp_growth hf hgf).comp
      (continuous_id.prodMk continuous_const)
  have hl : LipschitzOnWith (NNReal.mk C hC) (fun r => heatSolution f r x) (Ioo 0 H) := by
    apply Convex.lipschitzOnWith_of_nnNorm_deriv_le (s := Ioo 0 H)
      (fun r hr => (heat_time_transfer hf hfx hfxx hgf hgfx hgfxx hd hdd hr.1 x).differentiableAt)
      ?_ (convex_Ioo 0 H)
    intro r hr
    rw [(heat_time_transfer hf hfx hfxx hgf hgfx hgfxx hd hdd hr.1 x).deriv]
    exact_mod_cast hb r hr
  have hlc : LipschitzOnWith (NNReal.mk C hC) (fun r => heatSolution f r x) (Icc 0 H) := by
    simpa only [closure_Ioo hH.ne] using LipschitzOnWith.closure hcont.continuousOn hl
  have he (r : ℝ) : heatSolution f (max 0 r) x = heatSolution f r x := by
    by_cases hr : 0 ≤ r
    · rw [max_eq_right hr]
    · rw [max_eq_left (le_of_not_ge hr), heatSolution_of_nonpos f le_rfl,
        heatSolution_of_nonpos f (le_of_not_ge hr)]
  have hh := hlc.comp (LipschitzWith.id.const_max 0).lipschitzOnWith
    (show MapsTo (fun r : ℝ => max 0 r) (Iic H) (Icc 0 H) from
      fun r hr => ⟨le_max_left _ _, max_le hH.le hr⟩)
  change LipschitzOnWith (NNReal.mk C hC * 1) _ _ at hh
  rw [mul_one] at hh
  simpa only [Function.comp_def, id_eq, he] using hh

private theorem forcing_time_cont {f : ℝ → ℝ → ℝ} {T : ℝ}
    (hf : ContinuousOn (Function.uncurry f) (Icc 0 T ×ˢ univ)) (x : ℝ) :
    ContinuousOn (fun s => f s x) (Icc 0 T) :=
  hf.comp (continuous_id.prodMk continuous_const).continuousOn (fun _ hs => ⟨hs, mem_univ _⟩)

private theorem heat_integrand_cont {f : ℝ → ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hf : ContinuousOn (Function.uncurry f) (Icc 0 T ×ˢ univ))
    (hg : HeatWholeLine.HasExpGrowthOnStrip f T) (ν r x : ℝ) :
    ContinuousOn (fun s => heatSolution (f s) (ν * (r - s)) x) (Icc 0 T) :=
  (heatSolution_family_continuousOn hT hf hg).comp
    ((continuous_id.prodMk (continuous_const.mul (continuous_const.sub continuous_id))).prodMk
      continuous_const).continuousOn (fun _ hs => ⟨⟨hs, mem_univ _⟩, mem_univ _⟩)

private theorem heatDuhamel_fixed_interval {f : ℝ → ℝ → ℝ} {ν T : ℝ} (hν : 0 ≤ ν)
    (hf : ContinuousOn (Function.uncurry f) (Icc 0 T ×ˢ univ))
    (hg : HeatWholeLine.HasExpGrowthOnStrip f T) {t : ℝ} (ht : t ∈ Icc 0 T) (x : ℝ) :
    heatDuhamel ν f t x = (∫ s in 0..t, f s x) +
      ∫ s in 0..T, heatSolution (f s) (ν * (t - s)) x - f s x := by
  have hc := (heat_integrand_cont (ht.1.trans ht.2) hf hg ν t x).sub (forcing_time_cont hf x)
  have h0t : IntervalIntegrable
      (fun s => heatSolution (f s) (ν * (t - s)) x - f s x) volume 0 t :=
    (hc.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1
  have htT : IntervalIntegrable
      (fun s => heatSolution (f s) (ν * (t - s)) x - f s x) volume t T :=
    (hc.mono (Icc_subset_Icc ht.1 le_rfl)).intervalIntegrable_of_Icc ht.2
  have hz : (∫ s in t..T, heatSolution (f s) (ν * (t - s)) x - f s x) = 0 := by
    apply intervalIntegral.integral_zero_ae
    filter_upwards with s hs
    have hs' : t ≤ s := (show s ∈ Icc t T by
      simpa only [uIcc_of_le ht.2] using uIoc_subset_uIcc hs).1
    rw [heatSolution_of_nonpos _ (mul_nonpos_of_nonneg_of_nonpos hν (sub_nonpos.mpr hs'))]
    simp
  have he := intervalIntegral.integral_add_adjacent_intervals h0t htT
  rw [hz, add_zero] at he
  rw [← he, intervalIntegral.integral_sub (intervalIntegrable_heatDuhamel hf hg ν ht x)
    ((forcing_time_cont hf x).mono (Icc_subset_Icc le_rfl ht.2) |>.intervalIntegrable_of_Icc ht.1)]
  unfold heatDuhamel
  ring

/-- Spatial differentiation commutes with the Duhamel integral for jointly continuous
forcing and a jointly continuous spatial derivative, both with uniform exponential
growth on the closed strip. No second spatial or time derivative of the forcing is required. -/
theorem heatDuhamel_hasDerivAt_space {f fx : ℝ → ℝ → ℝ} {ν T : ℝ} (hν : 0 ≤ ν)
    (hf : ContinuousOn (Function.uncurry f) (Icc 0 T ×ˢ univ))
    (hfx : ContinuousOn (Function.uncurry fx) (Icc 0 T ×ˢ univ))
    (hgf : HeatWholeLine.HasExpGrowthOnStrip f T)
    (hgfx : HeatWholeLine.HasExpGrowthOnStrip fx T)
    (hd : ∀ s ∈ Icc 0 T, ∀ x, HasDerivAt (f s) (fx s x) x)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : ℝ) :
    HasDerivAt (heatDuhamel ν f t) (heatDuhamel ν fx t x) x := by
  have hheat (s : ℝ) (hs : s ∈ Icc 0 T) (y z : ℝ) :
      HasDerivAt (heatSolution (f s) y) (heatSolution (fx s) y z) z :=
    heat_transfer (slice_cont hfx hs) (slice_growth hgf hs) (slice_growth hgfx hs) (hd s hs) y z
  obtain ⟨M, c, hM, hc, hb⟩ := hgfx
  let J := ∫ y : ℝ, heatKernel ℝ 1 y * exp (c * sqrt (ν * T) * |y|)
  have hJ : 0 ≤ J := integral_nonneg (fun y =>
    mul_nonneg (heatKernel_pos one_pos y).le (exp_pos _).le)
  let C := M * J * exp (c * (|x| + 1))
  have hI (z : ℝ) := (intervalIntegrable_heatDuhamel hf hgf ν ht z).1
  have hIx := (intervalIntegrable_heatDuhamel hfx ⟨M,c,hM,hc,hb⟩ ν ht x).1
  have hresult := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioc 0 t))
    (F := fun z s => heatSolution (f s) (ν * (t - s)) z)
    (F' := fun z s => heatSolution (fx s) (ν * (t - s)) z)
    (s := Metric.ball x 1) (bound := fun _ => C)
    (Metric.ball_mem_nhds x (by norm_num))
    (Eventually.of_forall (fun z => (hI z).aestronglyMeasurable)) (hI x)
    hIx.aestronglyMeasurable ?_ (integrable_const C) ?_
  · change HasDerivAt (fun z => ∫ s in 0..t, heatSolution (f s) (ν * (t - s)) z)
      (∫ s in 0..t, heatSolution (fx s) (ν * (t - s)) x) x
    simpa only [intervalIntegral.integral_of_le ht.1] using hresult.2
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    intro z hz
    have hsT : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.trans ht.2⟩
    have hz' : |z - x| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using hz
    have hzR : |z| ≤ |x| + 1 := by
      have hh := abs_add_le (z - x) x
      rw [sub_add_cancel] at hh
      linarith
    have htime : ν * (t - s) ≤ ν * T :=
      mul_le_mul_of_nonneg_left ((sub_le_self t hs.1.le).trans ht.2) hν
    rw [Real.norm_eq_abs]
    exact (abs_heatSolution_le_exp_bound (slice_cont hfx hsT) hM hc (hb s hsT) htime z).trans
      (mul_le_mul_of_nonneg_left (exp_le_exp.mpr (mul_le_mul_of_nonneg_left hzR hc))
        (mul_nonneg hM hJ))
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    intro z _
    exact hheat s ⟨hs.1.le, hs.2.trans ht.2⟩ _ z

/-- A jointly continuous spatial derivative of the forcing with uniform exponential
growth gives a jointly continuous spatial derivative of the Duhamel field, up to time zero. -/
theorem heatDuhamel_deriv_continuousOn {f fx : ℝ → ℝ → ℝ} {ν T : ℝ}
    (hν : 0 ≤ ν) (hT : 0 ≤ T)
    (hf : ContinuousOn (Function.uncurry f) (Icc 0 T ×ˢ univ))
    (hfx : ContinuousOn (Function.uncurry fx) (Icc 0 T ×ˢ univ))
    (hgf : HeatWholeLine.HasExpGrowthOnStrip f T)
    (hgfx : HeatWholeLine.HasExpGrowthOnStrip fx T)
    (hd : ∀ s ∈ Icc 0 T, ∀ x, HasDerivAt (f s) (fx s x) x) :
    ContinuousOn (fun p : ℝ × ℝ => deriv (heatDuhamel ν f p.1) p.2)
      (Icc 0 T ×ˢ univ) := by
  apply (heatDuhamel_continuousOn hT hfx hgfx ν).congr
  intro p hp
  exact (heatDuhamel_hasDerivAt_space hν hf hfx hgf hgfx hd hp.1 p.2).deriv

/-- A second spatial derivative also passes through the Duhamel integral when the
forcing and both spatial derivatives are jointly continuous and grow at most exponentially,
uniformly on the closed time strip. No time derivative of the forcing is required. -/
theorem heatDuhamel_hasDerivAt_space_two {f fx fxx : ℝ → ℝ → ℝ} {ν T : ℝ}
    (hν : 0 ≤ ν)
    (hf : ContinuousOn (Function.uncurry f) (Icc 0 T ×ˢ univ))
    (hfx : ContinuousOn (Function.uncurry fx) (Icc 0 T ×ˢ univ))
    (hfxx : ContinuousOn (Function.uncurry fxx) (Icc 0 T ×ˢ univ))
    (hgf : HeatWholeLine.HasExpGrowthOnStrip f T)
    (hgfx : HeatWholeLine.HasExpGrowthOnStrip fx T)
    (hgfxx : HeatWholeLine.HasExpGrowthOnStrip fxx T)
    (hd : ∀ s ∈ Icc 0 T, ∀ x, HasDerivAt (f s) (fx s x) x)
    (hdd : ∀ s ∈ Icc 0 T, ∀ x, HasDerivAt (fx s) (fxx s x) x)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : ℝ) :
    HasDerivAt (deriv (heatDuhamel ν f t)) (heatDuhamel ν fxx t x) x := by
  have he : deriv (heatDuhamel ν f t) = heatDuhamel ν fx t :=
    funext (fun y => (heatDuhamel_hasDerivAt_space hν hf hfx hgf hgfx hd ht y).deriv)
  rw [he]
  exact heatDuhamel_hasDerivAt_space hν hfx hfxx hgfx hgfxx hdd ht x

/-- Classical time differentiation of the heat-kernel Duhamel integral on the open
strip. The forcing and its first two spatial derivatives must be jointly continuous
and uniformly exponentially bounded; no time derivative of the forcing is assumed. -/
theorem heatDuhamel_hasDerivAt_time {f fx fxx : ℝ → ℝ → ℝ} {ν T : ℝ}
    (hν : 0 < ν)
    (hf : ContinuousOn (Function.uncurry f) (Icc 0 T ×ˢ univ))
    (hfx : ContinuousOn (Function.uncurry fx) (Icc 0 T ×ˢ univ))
    (hfxx : ContinuousOn (Function.uncurry fxx) (Icc 0 T ×ˢ univ))
    (hgf : HeatWholeLine.HasExpGrowthOnStrip f T)
    (hgfx : HeatWholeLine.HasExpGrowthOnStrip fx T)
    (hgfxx : HeatWholeLine.HasExpGrowthOnStrip fxx T)
    (hd : ∀ s ∈ Icc 0 T, ∀ x, HasDerivAt (f s) (fx s x) x)
    (hdd : ∀ s ∈ Icc 0 T, ∀ x, HasDerivAt (fx s) (fxx s x) x)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (x : ℝ) :
    HasDerivAt (fun r => heatDuhamel ν f r x)
      (f t x + ν * heatDuhamel ν fxx t x) t := by
  have hT : 0 ≤ T := (ht.1.trans ht.2).le
  have ht' : t ∈ Icc 0 T := ⟨ht.1.le, ht.2.le⟩
  let F (r s : ℝ) := heatSolution (f s) (ν * (r - s)) x - f s x
  let F' := (Iic t).indicator (fun s => ν * heatSolution (fxx s) (ν * (t - s)) x)
  have hFc (r : ℝ) : ContinuousOn (F r) (Icc 0 T) :=
    (heat_integrand_cont hT hf hgf ν r x).sub (forcing_time_cont hf x)
  have hFi (r : ℝ) : Integrable (F r) (volume.restrict (Ioc 0 T)) :=
    ((hFc r).intervalIntegrable_of_Icc hT).1
  have hF'i : Integrable F' (volume.restrict (Ioc 0 T)) := by
    have hi := ((heat_integrand_cont hT hfxx hgfxx ν t x).intervalIntegrable_of_Icc
      (μ := volume) hT).1
    exact (hi.const_mul ν).indicator measurableSet_Iic
  obtain ⟨M, c, hM, hc, hb⟩ := hgfxx
  let J := ∫ y : ℝ, heatKernel ℝ 1 y * exp (c * sqrt (ν * T) * |y|)
  have hJ : 0 ≤ J := integral_nonneg (fun y =>
    mul_nonneg (heatKernel_pos one_pos y).le (exp_pos _).le)
  let C := M * J * exp (c * |x|)
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg hM hJ) (exp_pos _).le
  have hDiff := hasDerivAt_integral_of_dominated_loc_of_lip
    (μ := volume.restrict (Ioc 0 T)) (F := F) (F' := F')
    (s := Ioo 0 T) (bound := fun _ => ν * C) (Ioo_mem_nhds ht.1 ht.2)
    (Eventually.of_forall (fun r => (hFi r).aestronglyMeasurable)) (hFi t)
    hF'i.aestronglyMeasurable ?_ (integrable_const (ν * C)) ?_
  · have hD : HasDerivAt (fun r => ∫ s in 0..T, F r s)
        (ν * heatDuhamel ν fxx t x) t := by
      have hh := hDiff.2
      have he : (∫ s in 0..T, F' s) = ν * heatDuhamel ν fxx t x := by
        rw [show F' = {s | s ≤ t}.indicator
          (fun s => ν * heatSolution (fxx s) (ν * (t - s)) x) from rfl,
          intervalIntegral.integral_indicator ht', intervalIntegral.integral_const_mul]
        rfl
      rw [← he]
      simpa only [intervalIntegral.integral_of_le hT] using hh
    have hfc := forcing_time_cont hf x
    have hp := intervalIntegral.integral_hasDerivAt_right
      ((hfc.mono (Icc_subset_Icc le_rfl ht'.2)).intervalIntegrable_of_Icc ht'.1)
      ((hfc.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo t ht)
      (hfc.continuousAt (Icc_mem_nhds ht.1 ht.2))
    apply (hp.add hD).congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
    exact heatDuhamel_fixed_interval hν.le hf hgf ⟨hr.1.le, hr.2.le⟩ x
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hsT : s ∈ Icc 0 T := ⟨hs.1.le, hs.2⟩
    have hl := heat_time_lipschitz (slice_cont hf hsT) (slice_cont hfx hsT)
      (slice_cont hfxx hsT) (slice_growth hgf hsT) (slice_growth hgfx hsT)
      (slice_growth ⟨M,c,hM,hc,hb⟩ hsT) (hd s hsT) (hdd s hsT)
      (mul_pos hν (ht.1.trans ht.2)) hC x
      (fun r hr => abs_heatSolution_le_exp_bound (slice_cont hfxx hsT) hM hc (hb s hsT) hr.2.le x)
    apply LipschitzOnWith.of_dist_le_mul
    intro a ha b hb'
    have haH : ν * (a - s) ∈ Iic (ν * T) :=
      mul_le_mul_of_nonneg_left ((sub_le_self a hs.1.le).trans ha.2.le) hν.le
    have hbH : ν * (b - s) ∈ Iic (ν * T) :=
      mul_le_mul_of_nonneg_left ((sub_le_self b hs.1.le).trans hb'.2.le) hν.le
    have hh := hl.dist_le_mul _ haH _ hbH
    have he : dist (ν * (a - s)) (ν * (b - s)) = ν * dist a b := by
      simp only [Real.dist_eq, ← mul_sub, sub_sub_sub_cancel_right, abs_mul, abs_of_pos hν]
    rw [he] at hh
    change dist (heatSolution (f s) (ν * (a - s)) x - f s x)
      (heatSolution (f s) (ν * (b - s)) x - f s x) ≤ _
    rw [dist_sub_right]
    simpa only [NNReal.coe_mk, Real.coe_nnabs, abs_of_nonneg (mul_nonneg hν.le hC),
      mul_assoc, mul_comm, mul_left_comm] using hh
  · filter_upwards [ae_restrict_mem measurableSet_Ioc, (volume.restrict (Ioc 0 T)).ae_ne t]
      with s hs hst
    have hsT : s ∈ Icc 0 T := ⟨hs.1.le, hs.2⟩
    rcases lt_or_gt_of_ne hst with hst | hts
    · have hheat := heat_time_transfer (slice_cont hf hsT) (slice_cont hfx hsT)
        (slice_cont hfxx hsT) (slice_growth hgf hsT) (slice_growth hgfx hsT)
        (slice_growth ⟨M,c,hM,hc,hb⟩ hsT) (hd s hsT) (hdd s hsT)
        (mul_pos hν (sub_pos.mpr hst)) x
      have hh := (hheat.comp t (((hasDerivAt_id' t).sub_const s).const_mul ν)).sub_const (f s x)
      simpa only [F, F', mem_Iic, indicator_of_mem (show s ∈ Iic t from hst.le), Function.comp_def,
        mul_one, mul_comm] using hh
    · have he : (fun r => F r s) =ᶠ[𝓝 t] (fun _ => 0) := by
        filter_upwards [Iio_mem_nhds hts] with r hr
        dsimp only [F]
        rw [heatSolution_of_nonpos _ (mul_nonpos_of_nonneg_of_nonpos hν.le
          (sub_nonpos.mpr hr.le)), sub_self]
      simpa only [F', indicator_of_notMem (show s ∉ Iic t from not_le.mpr hts)] using
        (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq he

/-- The Duhamel integral satisfies the inhomogeneous heat equation with actual
ordinary time and second spatial derivatives at interior times. -/
theorem heatDuhamel_solves_heat {f fx fxx : ℝ → ℝ → ℝ} {ν T : ℝ}
    (hν : 0 < ν)
    (hf : ContinuousOn (Function.uncurry f) (Icc 0 T ×ˢ univ))
    (hfx : ContinuousOn (Function.uncurry fx) (Icc 0 T ×ˢ univ))
    (hfxx : ContinuousOn (Function.uncurry fxx) (Icc 0 T ×ˢ univ))
    (hgf : HeatWholeLine.HasExpGrowthOnStrip f T)
    (hgfx : HeatWholeLine.HasExpGrowthOnStrip fx T)
    (hgfxx : HeatWholeLine.HasExpGrowthOnStrip fxx T)
    (hd : ∀ s ∈ Icc 0 T, ∀ x, HasDerivAt (f s) (fx s x) x)
    (hdd : ∀ s ∈ Icc 0 T, ∀ x, HasDerivAt (fx s) (fxx s x) x)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (x : ℝ) :
    deriv (fun r => heatDuhamel ν f r x) t =
      ν * deriv (deriv (heatDuhamel ν f t)) x + f t x := by
  rw [(heatDuhamel_hasDerivAt_time hν hf hfx hfxx hgf hgfx hgfxx hd hdd ht x).deriv,
    (heatDuhamel_hasDerivAt_space_two hν.le hf hfx hfxx hgf hgfx hgfxx hd hdd
      ⟨ht.1.le, ht.2.le⟩ x).deriv, add_comm]

/-- The second spatial derivative is jointly continuous on the closed time strip,
including the zero initial trace, for continuous C2 spatial forcing of exponential growth. -/
theorem heatDuhamel_deriv_two_continuousOn {f fx fxx : ℝ → ℝ → ℝ} {ν T : ℝ}
    (hν : 0 ≤ ν) (hT : 0 ≤ T)
    (hf : ContinuousOn (Function.uncurry f) (Icc 0 T ×ˢ univ))
    (hfx : ContinuousOn (Function.uncurry fx) (Icc 0 T ×ˢ univ))
    (hfxx : ContinuousOn (Function.uncurry fxx) (Icc 0 T ×ˢ univ))
    (hgf : HeatWholeLine.HasExpGrowthOnStrip f T)
    (hgfx : HeatWholeLine.HasExpGrowthOnStrip fx T)
    (hgfxx : HeatWholeLine.HasExpGrowthOnStrip fxx T)
    (hd : ∀ s ∈ Icc 0 T, ∀ x, HasDerivAt (f s) (fx s x) x)
    (hdd : ∀ s ∈ Icc 0 T, ∀ x, HasDerivAt (fx s) (fxx s x) x) :
    ContinuousOn (fun p : ℝ × ℝ => deriv (deriv (heatDuhamel ν f p.1)) p.2)
      (Icc 0 T ×ˢ univ) := by
  apply (heatDuhamel_continuousOn hT hfxx hgfxx ν).congr
  intro p hp
  exact (heatDuhamel_hasDerivAt_space_two hν hf hfx hfxx hgf hgfx hgfxx hd hdd hp.1 p.2).deriv

/-- The actual time derivative is jointly continuous on the open strip. No
ordinary time derivative at either endpoint is claimed. -/
theorem heatDuhamel_time_deriv_continuousOn {f fx fxx : ℝ → ℝ → ℝ} {ν T : ℝ}
    (hν : 0 < ν) (hT : 0 ≤ T)
    (hf : ContinuousOn (Function.uncurry f) (Icc 0 T ×ˢ univ))
    (hfx : ContinuousOn (Function.uncurry fx) (Icc 0 T ×ˢ univ))
    (hfxx : ContinuousOn (Function.uncurry fxx) (Icc 0 T ×ˢ univ))
    (hgf : HeatWholeLine.HasExpGrowthOnStrip f T)
    (hgfx : HeatWholeLine.HasExpGrowthOnStrip fx T)
    (hgfxx : HeatWholeLine.HasExpGrowthOnStrip fxx T)
    (hd : ∀ s ∈ Icc 0 T, ∀ x, HasDerivAt (f s) (fx s x) x)
    (hdd : ∀ s ∈ Icc 0 T, ∀ x, HasDerivAt (fx s) (fxx s x) x) :
    ContinuousOn (fun p : ℝ × ℝ => deriv (fun r => heatDuhamel ν f r p.2) p.1)
      (Ioo 0 T ×ˢ univ) := by
  have hh := hf.add ((heatDuhamel_continuousOn hT hfxx hgfxx ν).const_mul ν)
  apply (hh.mono (prod_mono_left Ioo_subset_Icc_self)).congr
  intro p hp
  exact (heatDuhamel_hasDerivAt_time hν hf hfx hfxx hgf hgfx hgfxx hd hdd hp.1 p.2).deriv

end MathlibExt.Analysis.PDE.HeatKernel
