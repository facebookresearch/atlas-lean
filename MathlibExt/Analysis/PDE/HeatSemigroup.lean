/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PDE.HeatDuhamel
public import MathlibExt.Analysis.PDE.HeatKernelUniqueness
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Heat semigroup and time-integral interchange

The whole-line Gaussian evolution satisfies the semigroup law for continuous
initial data of exponential growth. The proof applies heat uniqueness to a time
shift of the original solution, including zero elapsed times. Uniform exponential
bounds also justify interchange of heat evolution with finite time integrals.

The uniqueness argument uses the exponential-growth special case of whole-line
heat uniqueness in Stanford Math 220B, *Heat Equation*, Theorem 20:
https://web.stanford.edu/class/math220b/handouts/heateqn.pdf.
-/

@[expose] public section

open MeasureTheory Set Real Filter Topology
open MathlibExt.Analysis
open scoped ContDiff

namespace MathlibExt.Analysis.PDE.HeatKernel

/-- Gaussian heat evolution composes by addition of nonnegative times for
continuous initial data of exponential growth. No initial derivative is required. -/
theorem heatSolution_semigroup_of_exp_growth {f : ℝ → ℝ} (hf : Continuous f) (hg : HasExpGrowth f)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (x : ℝ) :
    heatSolution (heatSolution f s) t x = heatSolution f (s + t) x := by
  have hcont := heatSolution_continuous_of_exp_growth hf hg
  have hfs : Continuous (heatSolution f s) :=
    hcont.comp (continuous_const.prodMk continuous_id)
  have hstrip := heatSolution_hasExpGrowthOnStrip hf hg (ν := 1) (by norm_num) (s + t)
  simp only [one_mul] at hstrip
  obtain ⟨M, c, hM, hc, hb⟩ := hstrip
  have hgs : HasExpGrowth (heatSolution f s) :=
    ⟨M, c, hM, hc, hb s ⟨hs, le_add_of_nonneg_right ht⟩⟩
  have hshift : HeatWholeLine.HasExpGrowthOnStrip (fun r y => heatSolution f (s + r) y) t :=
    ⟨M, c, hM, hc,fun r hr => hb (s + r) ⟨add_nonneg hs hr.1, add_le_add le_rfl hr.2⟩⟩
  have he := eq_heatSolution_of_exp_growth (u := fun r y => heatSolution f (s + r) y)
    (ut := fun r y => deriv (deriv (heatSolution f (s + r))) y)
    (ν := 1) (T := t) (by norm_num) hfs hgs
    (hcont.comp ((continuous_const.add continuous_fst).prodMk continuous_snd)).continuousOn
    (fun r hr y => ?_) (fun r hr y => ?_)
    (fun r hr y => by simp only [iteratedDeriv_succ, iteratedDeriv_zero, one_mul])
    hshift (fun y => by rw [add_zero]) t ⟨ht,le_rfl⟩ x
  · simpa only [one_mul] using he.symm
  · have hp : 0 < s + r := add_pos_of_nonneg_of_pos hs hr.1
    have hj := (heatSolution_contDiffOn_of_exp_growth hf.aestronglyMeasurable hg).contDiffAt
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds (show (s + r,y) ∈ Ioi 0 ×ˢ univ from
        ⟨hp, mem_univ y⟩))
    exact (hj.of_le (by simp)).comp y (contDiffAt_const.prodMk contDiffAt_id)
  · have hp : 0 < s + r := add_pos_of_nonneg_of_pos hs hr.1
    have hd := (heatSolution_hasDerivAt_time_of_exp_growth hf.aestronglyMeasurable hg hp y).comp r
      ((hasDerivAt_id' r).const_add s)
    simpa only [Function.comp_def, mul_one] using hd.hasDerivWithinAt (s := Iic r)

private theorem heatSolution_intervalIntegral_global {f : ℝ → ℝ → ℝ}
    (hf : Continuous (Function.uncurry f)) {M c : ℝ} (hM : 0 ≤ M) (hc : 0 ≤ c)
    (hb : ∀ s y, |f s y| ≤ M * exp (c * |y|)) (t h x : ℝ) :
    heatSolution (fun y => ∫ s in 0..t, f s y) h x =
      ∫ s in 0..t, heatSolution (f s) h x := by
  let : IsFiniteMeasure (volume.restrict (uIoc 0 t)) :=
    isFiniteMeasure_restrict.mpr (by rw [Real.volume_uIoc]; exact ENNReal.ofReal_ne_top)
  let A := M * exp (c * |x|)
  have hbound (s y : ℝ) : |f s (x - sqrt h * y)| ≤ A * exp ((c * sqrt h) * |y|) := by
    have ha : |x - sqrt h * y| ≤ |x| + sqrt h * |y| := by
      simpa only [abs_mul, abs_of_nonneg (sqrt_nonneg h)] using abs_sub x (sqrt h * y)
    calc
      _ ≤ M * exp (c * |x - sqrt h * y|) := hb s _
      _ ≤ M * exp (c * (|x| + sqrt h * |y|)) :=
        mul_le_mul_of_nonneg_left (exp_le_exp.mpr (mul_le_mul_of_nonneg_left ha hc)) hM
      _ = _ := by simp only [A, mul_add, exp_add, mul_assoc]
  have hcont : Continuous (fun p : ℝ × ℝ =>
      heatKernel ℝ 1 p.2 * f p.1 (x - sqrt h * p.2)) :=
    ((heatKernel_contDiff 1).continuous.comp continuous_snd).mul
      (hf.comp (continuous_fst.prodMk
        (continuous_const.sub (continuous_const.mul continuous_snd))))
  have hprod : Integrable (fun p : ℝ × ℝ =>
      heatKernel ℝ 1 p.2 * f p.1 (x - sqrt h * p.2))
      ((volume.restrict (uIoc 0 t)).prod volume) := by
    apply (((integrable_heatKernel_exp_abs one_pos (c * sqrt h)).const_mul A).comp_snd
      (volume.restrict (uIoc 0 t))).mono' hcont.aestronglyMeasurable
    filter_upwards with p
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (heatKernel_pos one_pos p.2)]
    calc
      _ ≤ heatKernel ℝ 1 p.2 * (A * exp ((c * sqrt h) * |p.2|)) :=
        mul_le_mul_of_nonneg_left (hbound p.1 p.2) (heatKernel_pos one_pos p.2).le
      _ = _ := by ring
  have he := intervalIntegral_integral_swap (a := 0) (b := t) (μ := volume)
    (f := fun s y => heatKernel ℝ 1 y * f s (x - sqrt h * y)) hprod
  simp_rw [heatSolution_rescaled_all, ← intervalIntegral.integral_const_mul]
  exact he.symm

/-- Heat evolution commutes with a finite time integral of a jointly continuous
family with uniform exponential growth. The family need only be continuous on
its closed time strip; the heat parameter may use the stationary extension. -/
theorem heatSolution_intervalIntegral_of_exp_growth {f : ℝ → ℝ → ℝ} {T t : ℝ}
    (hf : ContinuousOn (Function.uncurry f) (Icc 0 T ×ˢ univ))
    (hg : HeatWholeLine.HasExpGrowthOnStrip f T) (ht : t ∈ Icc 0 T) (h x : ℝ) :
    heatSolution (fun y => ∫ s in 0..t, f s y) h x =
      ∫ s in 0..t, heatSolution (f s) h x := by
  let g (s y : ℝ) := f (max 0 (min T s)) y
  have hm (s : ℝ) : max 0 (min T s) ∈ Icc 0 T :=
    ⟨le_max_left _ _, max_le (ht.1.trans ht.2) (min_le_left _ _)⟩
  have hgcont : Continuous (Function.uncurry g) :=
    hf.comp_continuous
      ((continuous_const.max (continuous_const.min continuous_fst)).prodMk continuous_snd)
      (fun p => ⟨hm p.1, mem_univ p.2⟩)
  obtain ⟨M, c, hM, hc, hb⟩ := hg
  have he := heatSolution_intervalIntegral_global hgcont hM hc (fun s y => hb _ (hm s) y) t h x
  have heq (s : ℝ) (hs : s ∈ uIcc 0 t) : g s = f s := by
    have hs' : s ∈ Icc 0 t := by simpa only [uIcc_of_le ht.1] using hs
    funext y
    dsimp only [g]
    rw [min_eq_right (hs'.2.trans ht.2), max_eq_right hs'.1]
  have hi : (fun y => ∫ s in 0..t, g s y) = fun y => ∫ s in 0..t, f s y := by
    funext y
    exact intervalIntegral.integral_congr (fun s hs => congrFun (heq s hs) y)
  rw [hi] at he
  exact he.trans (intervalIntegral.integral_congr (fun s hs => by rw [heq s hs]))

/-- Applying additional nonnegative heat evolution to a Duhamel value adds that
heat time inside the forcing integral. All integrability follows from continuity
and uniform exponential growth of the forcing. -/
theorem heatSolution_heatDuhamel {f : ℝ → ℝ → ℝ} {ν T t h : ℝ}
    (hν : 0 ≤ ν)
    (hf : ContinuousOn (Function.uncurry f) (Icc 0 T ×ˢ univ))
    (hg : HeatWholeLine.HasExpGrowthOnStrip f T) (ht : t ∈ Icc 0 T) (hh : 0 ≤ h) (x : ℝ) :
    heatSolution (heatDuhamel ν f t) h x =
      ∫ s in 0..t, heatSolution (f s) (ν * (t - s) + h) x := by
  let g (s y : ℝ) := heatSolution (f s) (ν * (t - s)) y
  have hgc : ContinuousOn (Function.uncurry g) (Icc 0 t ×ˢ univ) :=
    (heatSolution_family_continuousOn (ht.1.trans ht.2) hf hg).comp
      (((continuous_fst.prodMk
        (continuous_const.mul (continuous_const.sub continuous_fst))).prodMk
          continuous_snd).continuousOn)
      (fun p hp => ⟨⟨⟨hp.1.1, hp.1.2.trans ht.2⟩, mem_univ _⟩, mem_univ _⟩)
  obtain ⟨M, c, hM, hc, hb⟩ := hg
  let J := ∫ y : ℝ, heatKernel ℝ 1 y * exp (c * sqrt (ν * T) * |y|)
  have hJ : 0 ≤ J := integral_nonneg (fun y =>
    mul_nonneg (heatKernel_pos one_pos y).le (exp_pos _).le)
  have hgg : HeatWholeLine.HasExpGrowthOnStrip g t := by
    refine ⟨M * J, c, mul_nonneg hM hJ, hc, fun s hs y => ?_⟩
    have hsT : s ∈ Icc 0 T := ⟨hs.1, hs.2.trans ht.2⟩
    have hfs : Continuous (f s) := hf.comp_continuous
      (continuous_const.prodMk continuous_id) (fun y => ⟨hsT, mem_univ y⟩)
    exact abs_heatSolution_le_exp_bound hfs hM hc (hb s hsT)
      (mul_le_mul_of_nonneg_left ((sub_le_self t hs.1).trans ht.2) hν) y
  have he := heatSolution_intervalIntegral_of_exp_growth hgc hgg ⟨ht.1, le_rfl⟩ h x
  change heatSolution (heatDuhamel ν f t) h x = ∫ s in 0..t, heatSolution (g s) h x at he
  refine he.trans (intervalIntegral.integral_congr ?_)
  intro s hs
  have hs' : s ∈ Icc 0 t := by simpa only [uIcc_of_le ht.1] using hs
  have hsT : s ∈ Icc 0 T := ⟨hs'.1, hs'.2.trans ht.2⟩
  have hfs : Continuous (f s) := hf.comp_continuous
    (continuous_const.prodMk continuous_id) (fun y => ⟨hsT, mem_univ y⟩)
  exact heatSolution_semigroup_of_exp_growth hfs ⟨M, c, hM, hc, hb s hsT⟩
    (mul_nonneg hν (sub_nonneg.mpr hs'.2)) hh x

/-- Restart the Duhamel integral at a nonnegative time: evolve the accumulated
value by the heat semigroup and add the shifted forcing over the remaining time.
The forcing need only be jointly continuous with uniform exponential growth. -/
theorem heatDuhamel_restart {f : ℝ → ℝ → ℝ} {ν T a b : ℝ}
    (hν : 0 ≤ ν)
    (hf : ContinuousOn (Function.uncurry f) (Icc 0 T ×ˢ univ))
    (hg : HeatWholeLine.HasExpGrowthOnStrip f T)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ T) (x : ℝ) :
    heatDuhamel ν f (a + b) x = heatSolution (heatDuhamel ν f a) (ν * b) x +
      heatDuhamel ν (fun s => f (a + s)) b x := by
  have haT : a ∈ Icc 0 T := ⟨ha, (le_add_of_nonneg_right hb).trans hab⟩
  have hi := intervalIntegrable_heatDuhamel hf hg ν ⟨add_nonneg ha hb, hab⟩ x
  have hi0 : IntervalIntegrable (fun s => heatSolution (f s) (ν * (a + b - s)) x) volume 0 a :=
    hi.mono_set (by simpa only [uIcc_of_le ha, uIcc_of_le (add_nonneg ha hb)] using
      Icc_subset_Icc le_rfl (le_add_of_nonneg_right hb : a ≤ a + b))
  have hi1 : IntervalIntegrable
      (fun s => heatSolution (f s) (ν * (a + b - s)) x) volume a (a + b) :=
    hi.mono_set (by
      simpa only [uIcc_of_le (le_add_of_nonneg_right hb),
        uIcc_of_le (add_nonneg ha hb)] using Icc_subset_Icc ha (le_refl (a + b)))
  have he0 : (∫ s in 0..a, heatSolution (f s) (ν * (a + b - s)) x) =
      heatSolution (heatDuhamel ν f a) (ν * b) x := by
    rw [heatSolution_heatDuhamel hν hf hg haT (mul_nonneg hν hb)]
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only
    rw [show ν * (a + b - s) = ν * (a - s) + ν * b by ring]
  have he1 : (∫ s in a..a + b, heatSolution (f s) (ν * (a + b - s)) x) =
      heatDuhamel ν (fun s => f (a + s)) b x := by
    have he := intervalIntegral.integral_comp_add_left
      (fun s => heatSolution (f s) (ν * (a + b - s)) x) a (a := 0) (b := b)
    rw [add_zero] at he
    rw [← he]
    unfold heatDuhamel
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only
    rw [show a + b - (a + s) = b - s by ring]
  change (∫ s in 0..a + b, heatSolution (f s) (ν * (a + b - s)) x) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals hi0 hi1, he0, he1]

/-- Restart the full inhomogeneous heat construction, including its freely
evolved initial data. Only continuity and exponential growth are required for
initial data and forcing; no classical differentiability is assumed. -/
theorem heatSolution_add_heatDuhamel_restart {g : ℝ → ℝ} {f : ℝ → ℝ → ℝ} {ν T a b : ℝ}
    (hν : 0 ≤ ν) (hgc : Continuous g) (hgg : HasExpGrowth g)
    (hf : ContinuousOn (Function.uncurry f) (Icc 0 T ×ˢ univ))
    (hg : HeatWholeLine.HasExpGrowthOnStrip f T)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ T) (x : ℝ) :
    heatSolution g (ν * (a + b)) x + heatDuhamel ν f (a + b) x =
      heatSolution (fun y => heatSolution g (ν * a) y + heatDuhamel ν f a y) (ν * b) x +
        heatDuhamel ν (fun s => f (a + s)) b x := by
  have hT : 0 ≤ T := (add_nonneg ha hb).trans hab
  have haT : a ∈ Icc 0 T := ⟨ha, (le_add_of_nonneg_right hb).trans hab⟩
  have hpc : Continuous (heatSolution g (ν * a)) :=
    (heatSolution_continuous_of_exp_growth hgc hgg).comp
      (continuous_const.prodMk continuous_id)
  have hpg : HasExpGrowth (heatSolution g (ν * a)) := by
    obtain ⟨M, c, hM, hc, hbd⟩ := heatSolution_hasExpGrowthOnStrip hgc hgg hν T
    exact ⟨M, c, hM, hc, hbd a haT⟩
  have hdc : Continuous (heatDuhamel ν f a) :=
    (heatDuhamel_continuousOn hT hf hg ν).comp_continuous
      (continuous_const.prodMk continuous_id) (fun y => ⟨haT, mem_univ y⟩)
  have hdg : HasExpGrowth (heatDuhamel ν f a) := by
    obtain ⟨M, c, hM, hc, hbd⟩ := heatDuhamel_hasExpGrowthOnStrip hf hg hν hT
    exact ⟨M, c, hM, hc, hbd a haT⟩
  rw [heatSolution_add_of_exp_growth hpc hdc hpg hdg,
    heatSolution_semigroup_of_exp_growth hgc hgg (mul_nonneg hν ha) (mul_nonneg hν hb),
    heatDuhamel_restart hν hf hg ha hb hab, mul_add, add_assoc]

end MathlibExt.Analysis.PDE.HeatKernel
