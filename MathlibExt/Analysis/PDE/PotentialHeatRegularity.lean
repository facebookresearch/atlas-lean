/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PDE.PotentialHeatSeries
public import MathlibExt.Analysis.PDE.HeatDuhamelSmoothing
import MathlibExt.Analysis.PDE.HeatSemigroup
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Restart and spatial regularity of potential-heat evolution

The constructed Volterra field restarts from each nonnegative-time slice.
Positive viscosity gives an actual spatial derivative from continuous data,
with uniform exponential growth away from time zero. For `C¹` initial data and
exponential growth of its derivative, joint derivative continuity extends to
initial time. No derivative of the bounded continuous potential is required.

The analytic starting points are Gaussian differentiation and Duhamel's formula
in James Nolen, *Partial Differential Equations and Diffusion Processes*,
§§2.3–2.4, https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf.
The weighted derivative conclusions follow by applying these estimates to the
convergent Volterra field. No classical PDE or higher regularity is asserted here.
-/

@[expose] public section

open MeasureTheory Set Real Filter Topology
open MathlibExt.Analysis

namespace MathlibExt.Analysis.PDE.HeatKernel

private theorem forcing_regular {q : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {ν T Q : ℝ}
    (hν : 0 ≤ ν) (hT : 0 ≤ T)
    (hq : ContinuousOn (Function.uncurry q) (Icc 0 T ×ˢ univ))
    (hQ : 0 ≤ Q) (hqb : ∀ t ∈ Icc 0 T, ∀ x, |q t x| ≤ Q)
    (hg : Continuous g) (hgg : HasExpGrowth g) :
    ContinuousOn (Function.uncurry (fun s y => q s y * potentialHeatSolution ν q g s y))
      (Icc 0 T ×ˢ univ) ∧
    HeatWholeLine.HasExpGrowthOnStrip (fun s y => q s y * potentialHeatSolution ν q g s y) T := by
  refine ⟨hq.mul (potentialHeatSolution_continuousOn hν hT hq hQ hqb hg hgg), ?_⟩
  obtain ⟨M,c,hM,hc,hb⟩ := potentialHeatSolution_hasExpGrowthOnStrip hν hq hQ hqb hg hgg
  refine ⟨Q*M,c,mul_nonneg hQ hM,hc,fun s hs y => ?_⟩
  rw [abs_mul,mul_assoc]
  exact mul_le_mul (hqb s hs y) (hb s hs y) (abs_nonneg _) hQ

/-- Potential-heat evolution satisfies a mild equation restarted at any
nonnegative time, with the actual solution slice as new initial data. -/
theorem potentialHeatSolution_restart_mild {q : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {ν T Q a b : ℝ}
    (hν : 0 ≤ ν) (hq : ContinuousOn (Function.uncurry q) (Icc 0 T ×ˢ univ))
    (hQ : 0 ≤ Q) (hqb : ∀ t ∈ Icc 0 T, ∀ x, |q t x| ≤ Q)
    (hg : Continuous g) (hgg : HasExpGrowth g)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ T) (x : ℝ) :
    potentialHeatSolution ν q g (a+b) x =
      heatSolution (potentialHeatSolution ν q g a) (ν*b) x +
        heatDuhamel ν (fun s y => q (a+s) y * potentialHeatSolution ν q g (a+s) y) b x := by
  have hT := (add_nonneg ha hb).trans hab
  obtain ⟨hfc,hfg⟩ := forcing_regular hν hT hq hQ hqb hg hgg
  have h := heatSolution_add_heatDuhamel_restart hν hg hgg hfc hfg ha hb hab x
  rw [← potentialHeatSolution_mild hν hq hQ hqb hg hgg ⟨add_nonneg ha hb,hab⟩ x] at h
  have he : (fun y => heatSolution g (ν*a) y +
      heatDuhamel ν (fun s z => q s z * potentialHeatSolution ν q g s z) a y) =
        potentialHeatSolution ν q g a := by
    funext y
    exact (potentialHeatSolution_mild hν hq hQ hqb hg hgg
      ⟨ha,(le_add_of_nonneg_right hb).trans hab⟩ y).symm
  rw [he] at h
  exact h

/-- Restarting the actual field agrees with the Volterra construction for the
shifted potential and the actual initial slice. -/
theorem potentialHeatSolution_restart {q : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {ν T Q a b : ℝ}
    (hν : 0 ≤ ν) (hq : ContinuousOn (Function.uncurry q) (Icc 0 T ×ˢ univ))
    (hQ : 0 ≤ Q) (hqb : ∀ t ∈ Icc 0 T, ∀ x, |q t x| ≤ Q)
    (hg : Continuous g) (hgg : HasExpGrowth g)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ T) (x : ℝ) :
    potentialHeatSolution ν q g (a+b) x =
      potentialHeatSolution ν (fun s y => q (a+s) y) (potentialHeatSolution ν q g a) b x := by
  have haT : a ∈ Icc 0 T := ⟨ha,(le_add_of_nonneg_right hb).trans hab⟩
  have hT := ha.trans haT.2
  have hc := potentialHeatSolution_continuousOn hν hT hq hQ hqb hg hgg
  have hgrowth := potentialHeatSolution_hasExpGrowthOnStrip hν hq hQ hqb hg hgg
  have hshift (p : ℝ × ℝ) (hp : p ∈ Icc 0 (T-a) ×ˢ univ) :
      (a+p.1,p.2) ∈ Icc 0 T ×ˢ univ :=
    ⟨⟨add_nonneg ha hp.1.1,by linarith [hp.1.2]⟩,mem_univ _⟩
  have hmap : Continuous (fun p : ℝ × ℝ => (a+p.1,p.2)) := by fun_prop
  have hqa : ContinuousOn (Function.uncurry (fun s y => q (a+s) y))
      (Icc 0 (T-a) ×ˢ univ) := hq.comp hmap.continuousOn hshift
  have hua : ContinuousOn (Function.uncurry (fun s y => potentialHeatSolution ν q g (a+s) y))
      (Icc 0 (T-a) ×ˢ univ) := hc.comp hmap.continuousOn hshift
  have hga : Continuous (potentialHeatSolution ν q g a) := hc.comp_continuous
    (continuous_const.prodMk continuous_id) (fun y => ⟨haT,mem_univ y⟩)
  obtain ⟨M,c,hM,hc',hbound⟩ := hgrowth
  have hgag : HasExpGrowth (potentialHeatSolution ν q g a) := ⟨M,c,hM,hc',hbound a haT⟩
  have huag : HeatWholeLine.HasExpGrowthOnStrip
      (fun s y => potentialHeatSolution ν q g (a+s) y) (T-a) := by
    refine ⟨M,c,hM,hc',fun s hs y => ?_⟩
    exact hbound _ (hshift (s,y) ⟨hs,mem_univ _⟩).1 y
  apply eq_potentialHeatSolution_of_mild (T := T-a) hν hqa hQ ?_ hga hgag hua huag ?_
    ⟨hb,by linarith⟩ x
  · intro s hs y
    exact hqb _ (hshift (s,y) ⟨hs,mem_univ _⟩).1 y
  · intro s hs y
    exact potentialHeatSolution_restart_mild hν hq hQ hqb hg hgg ha hs.1
      (by linarith [hs.2]) y

/-- Continuous initial data and a bounded continuous potential give an actual
spatial derivative at positive time; no derivative of the potential is required. -/
theorem potentialHeatSolution_hasDerivAt_space_of_continuous
    {q : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {ν T Q t : ℝ}
    (hν : 0 < ν) (hq : ContinuousOn (Function.uncurry q) (Icc 0 T ×ˢ univ))
    (hQ : 0 ≤ Q) (hqb : ∀ t ∈ Icc 0 T, ∀ x, |q t x| ≤ Q)
    (hg : Continuous g) (hgg : HasExpGrowth g) (ht : t ∈ Ioc 0 T) (x : ℝ) :
    HasDerivAt (potentialHeatSolution ν q g t)
      (deriv (heatSolution g (ν*t)) x +
        deriv (heatDuhamel ν (fun s y => q s y * potentialHeatSolution ν q g s y) t) x) x := by
  obtain ⟨hfc,hfg⟩ := forcing_regular hν.le (ht.1.le.trans ht.2) hq hQ hqb hg hgg
  have hd := (heatDuhamel_hasDerivAt_space_of_continuous hν hfc hfg
    ⟨ht.1.le,ht.2⟩ x).differentiableAt.hasDerivAt
  have hp := (heatSolution_hasDerivAt_space_of_exp_growth hg.aestronglyMeasurable hgg
    (mul_pos hν ht.1) x).differentiableAt.hasDerivAt
  have he : potentialHeatSolution ν q g t = fun y => heatSolution g (ν*t) y +
      heatDuhamel ν (fun s z => q s z * potentialHeatSolution ν q g s z) t y :=
    funext (potentialHeatSolution_mild hν.le hq hQ hqb hg hgg ⟨ht.1.le,ht.2⟩)
  rw [he]
  exact hp.add hd



private theorem continuousOn_heat_deriv {g : ℝ → ℝ} {ν : ℝ}
    (hν : 0 < ν) (hg : Continuous g) (hgg : HasExpGrowth g) :
    ContinuousOn (fun p : ℝ × ℝ => deriv (heatSolution g (ν*p.1)) p.2) (Ioi 0 ×ˢ univ) := by
  have h := heatSolution_contDiffOn_scaled_of_exp_growth hg.aestronglyMeasurable hgg hν
  have hcont := ((h.fderiv_of_isOpen (isOpen_Ioi.prod isOpen_univ)
    (m := 0) (by simp)).clm_apply (contDiffOn_const (c := ((0,1) : ℝ × ℝ)))).continuousOn
  apply hcont.congr
  intro p hp
  have hd := ((h.contDiffAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds hp)).differentiableAt
    (by simp)).hasFDerivAt.comp_hasDerivAt p.2
      ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
  simpa only [Function.comp_def, id_eq] using hd.deriv

/-- The actual spatial derivative is jointly continuous on each positive-time
strip, including its terminal time, for a merely continuous bounded potential. -/
theorem potentialHeatSolution_deriv_continuousOn
    {q : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {ν T Q : ℝ}
    (hν : 0 < ν) (hq : ContinuousOn (Function.uncurry q) (Icc 0 T ×ˢ univ))
    (hQ : 0 ≤ Q) (hqb : ∀ t ∈ Icc 0 T, ∀ x, |q t x| ≤ Q)
    (hg : Continuous g) (hgg : HasExpGrowth g) :
    ContinuousOn (fun p : ℝ × ℝ => deriv (potentialHeatSolution ν q g p.1) p.2)
      (Ioc 0 T ×ˢ univ) := by
  by_cases hT : 0 ≤ T
  · obtain ⟨hfc,hfg⟩ := forcing_regular hν.le hT hq hQ hqb hg hgg
    have hp := (continuousOn_heat_deriv hν hg hgg).mono
      (show Ioc 0 T ×ˢ univ ⊆ Ioi 0 ×ˢ univ from fun p hp => ⟨hp.1.1,hp.2⟩)
    have hd := (heatDuhamel_deriv_continuousOn_of_continuous hν hT hfc hfg).mono
      (show Ioc 0 T ×ˢ univ ⊆ Icc 0 T ×ˢ univ from fun p hp => ⟨⟨hp.1.1.le,hp.1.2⟩,hp.2⟩)
    exact (hp.add hd).congr (fun p hp =>
      (potentialHeatSolution_hasDerivAt_space_of_continuous hν hq hQ hqb hg hgg hp.1 p.2).deriv)
  · intro p hp
    exact (hT (hp.1.1.le.trans hp.1.2)).elim

/-- For `C¹` initial data with exponentially growing derivative, spatial
smoothing has a derivative-transfer formula down to time zero. -/
theorem potentialHeatSolution_hasDerivAt_space_of_contDiff
    {q : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {ν T Q t : ℝ}
    (hν : 0 < ν) (hq : ContinuousOn (Function.uncurry q) (Icc 0 T ×ˢ univ))
    (hQ : 0 ≤ Q) (hqb : ∀ t ∈ Icc 0 T, ∀ x, |q t x| ≤ Q)
    (hg : ContDiff ℝ 1 g) (hgg : HasExpGrowth g) (hgd : HasExpGrowth (deriv g))
    (ht : t ∈ Icc 0 T) (x : ℝ) :
    HasDerivAt (potentialHeatSolution ν q g t)
      (heatSolution (deriv g) (ν*t) x +
        deriv (heatDuhamel ν (fun s y => q s y * potentialHeatSolution ν q g s y) t) x) x := by
  obtain ⟨hfc,hfg⟩ := forcing_regular hν.le (ht.1.trans ht.2) hq hQ hqb hg.continuous hgg
  have hd :=
    (heatDuhamel_hasDerivAt_space_of_continuous hν hfc hfg ht x).differentiableAt.hasDerivAt
  have hp := heatSolution_hasDerivAt_deriv_of_exp_growth hg hgg hgd (ν*t) x
  have he : potentialHeatSolution ν q g t = fun y => heatSolution g (ν*t) y +
      heatDuhamel ν (fun s z => q s z * potentialHeatSolution ν q g s z) t y :=
    funext (potentialHeatSolution_mild hν.le hq hQ hqb hg.continuous hgg ht)
  rw [he]
  exact hp.add hd

/-- With `C¹` exponentially growing initial data and derivative, the actual
spatial derivative is jointly continuous on the closed time strip. -/
theorem potentialHeatSolution_deriv_continuousOn_of_contDiff
    {q : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {ν T Q : ℝ}
    (hν : 0 < ν) (hT : 0 ≤ T)
    (hq : ContinuousOn (Function.uncurry q) (Icc 0 T ×ˢ univ))
    (hQ : 0 ≤ Q) (hqb : ∀ t ∈ Icc 0 T, ∀ x, |q t x| ≤ Q)
    (hg : ContDiff ℝ 1 g) (hgg : HasExpGrowth g) (hgd : HasExpGrowth (deriv g)) :
    ContinuousOn (fun p : ℝ × ℝ => deriv (potentialHeatSolution ν q g p.1) p.2)
      (Icc 0 T ×ˢ univ) := by
  obtain ⟨hfc,hfg⟩ := forcing_regular hν.le hT hq hQ hqb hg.continuous hgg
  have hp : ContinuousOn (fun p : ℝ × ℝ => heatSolution (deriv g) (ν*p.1) p.2)
      (Icc 0 T ×ˢ univ) :=
    ((heatSolution_continuous_of_exp_growth hg.continuous_deriv_one hgd).comp
    ((continuous_const.mul continuous_fst).prodMk continuous_snd)).continuousOn
  have hd := heatDuhamel_deriv_continuousOn_of_continuous hν hT hfc hfg
  exact (hp.add hd).congr (fun p hp =>
    (potentialHeatSolution_hasDerivAt_space_of_contDiff hν hq hQ hqb hg hgg hgd hp.1 p.2).deriv)



private theorem growth_add {u v : ℝ → ℝ → ℝ} {T : ℝ}
    (hu : HeatWholeLine.HasExpGrowthOnStrip u T) (hv : HeatWholeLine.HasExpGrowthOnStrip v T) :
    HeatWholeLine.HasExpGrowthOnStrip (fun t x => u t x + v t x) T := by
  obtain ⟨M,c,hM,hc,hb⟩ := hv
  have hn : HeatWholeLine.HasExpGrowthOnStrip (fun t x => -v t x) T :=
    ⟨M,c,hM,hc,fun t ht x => by simpa only [abs_neg] using hb t ht x⟩
  simpa only [sub_neg_eq_add] using hu.sub hn

/-- The actual spatial derivative has a uniform exponential growth bound on
any finite strip separated from initial time. The strip is parametrized by its
elapsed time after the positive lower endpoint. -/
theorem potentialHeatSolution_deriv_hasExpGrowthOnStrip
    {q : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {ν T Q a : ℝ}
    (hν : 0 < ν) (hq : ContinuousOn (Function.uncurry q) (Icc 0 T ×ˢ univ))
    (hQ : 0 ≤ Q) (hqb : ∀ t ∈ Icc 0 T, ∀ x, |q t x| ≤ Q)
    (hg : Continuous g) (hgg : HasExpGrowth g) (ha : 0 < a) (haT : a ≤ T) :
    HeatWholeLine.HasExpGrowthOnStrip
      (fun s x => deriv (potentialHeatSolution ν q g (a+s)) x) (T-a) := by
  have hT := ha.le.trans haT
  have hshift {s : ℝ} (hs : s ∈ Icc 0 (T-a)) : a+s ∈ Ioc 0 T :=
    ⟨add_pos_of_pos_of_nonneg ha hs.1,by linarith [hs.2]⟩
  obtain ⟨hfc,hfg⟩ := forcing_regular hν.le hT hq hQ hqb hg hgg
  have hd := heatDuhamel_deriv_hasExpGrowthOnStrip hν hfc hfg
  have hds : HeatWholeLine.HasExpGrowthOnStrip
      (fun s x => deriv (heatDuhamel ν (fun r y => q r y * potentialHeatSolution ν q g r y)
        (a+s)) x) (T-a) := by
    obtain ⟨N,d,hN,hd,hb⟩ := hd
    exact ⟨N,d,hN,hd,fun s hs x => hb (a+s) ⟨(hshift hs).1.le,(hshift hs).2⟩ x⟩
  have hps : HeatWholeLine.HasExpGrowthOnStrip
      (fun s x => deriv (heatSolution g (ν*(a+s))) x) (T-a) := by
    obtain ⟨M,c,hM,hc,hb⟩ := hgg
    let J := ∫ y : ℝ, |y| * heatKernel ℝ 1 y * exp (c * sqrt (ν*T) * |y|)
    have hJ : 0 ≤ J := integral_nonneg (fun y =>
      mul_nonneg (mul_nonneg (abs_nonneg _) (heatKernel_pos one_pos _).le) (exp_pos _).le)
    refine ⟨(M / (2 * sqrt (ν*a))) * J,c,by positivity,hc,fun s hs x => ?_⟩
    have htime := hshift hs
    have hh := abs_heatSolution_deriv_le_exp_bound hg hM hc hb
      (mul_pos hν htime.1) (mul_le_mul_of_nonneg_left htime.2 hν.le) x
    have hden : M / (2 * sqrt (ν*(a+s))) ≤ M / (2 * sqrt (ν*a)) :=
      div_le_div_of_nonneg_left hM
        (mul_pos (by norm_num) (sqrt_pos.mpr (mul_pos hν ha)))
        (mul_le_mul_of_nonneg_left
          (sqrt_le_sqrt (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hs.1) hν.le))
          (by norm_num))
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hden hJ) (exp_pos _).le)
  obtain ⟨M,c,hM,hc,hb⟩ := growth_add hps hds
  refine ⟨M,c,hM,hc,fun s hs x => ?_⟩
  dsimp only
  rw [(potentialHeatSolution_hasDerivAt_space_of_continuous hν hq hQ hqb hg hgg
    (hshift hs) x).deriv]
  exact hb s hs x

/-- `C¹` data with an exponentially growing derivative give a derivative bound
uniform on the entire closed strip, including initial time. -/
theorem potentialHeatSolution_deriv_hasExpGrowthOnStrip_of_contDiff
    {q : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {ν T Q : ℝ}
    (hν : 0 < ν) (hT : 0 ≤ T)
    (hq : ContinuousOn (Function.uncurry q) (Icc 0 T ×ˢ univ))
    (hQ : 0 ≤ Q) (hqb : ∀ t ∈ Icc 0 T, ∀ x, |q t x| ≤ Q)
    (hg : ContDiff ℝ 1 g) (hgg : HasExpGrowth g) (hgd : HasExpGrowth (deriv g)) :
    HeatWholeLine.HasExpGrowthOnStrip (fun t x => deriv (potentialHeatSolution ν q g t) x) T := by
  obtain ⟨hfc,hfg⟩ := forcing_regular hν.le hT hq hQ hqb hg.continuous hgg
  have hd := heatDuhamel_deriv_hasExpGrowthOnStrip hν hfc hfg
  have hp := heatSolution_hasExpGrowthOnStrip hg.continuous_deriv_one hgd hν.le T
  obtain ⟨M,c,hM,hc,hb⟩ := growth_add hp hd
  refine ⟨M,c,hM,hc,fun t ht x => ?_⟩
  dsimp only
  rw [(potentialHeatSolution_hasDerivAt_space_of_contDiff hν hq hQ hqb hg hgg hgd ht x).deriv]
  exact hb t ht x

/-- Joint approach to initial time recovers the actual initial derivative for
`C¹` data and exponential growth of both the datum and its derivative. -/
theorem potentialHeatSolution_deriv_tendsto_initial
    {q : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {ν T Q : ℝ}
    (hν : 0 < ν) (hT : 0 ≤ T)
    (hq : ContinuousOn (Function.uncurry q) (Icc 0 T ×ˢ univ))
    (hQ : 0 ≤ Q) (hqb : ∀ t ∈ Icc 0 T, ∀ x, |q t x| ≤ Q)
    (hg : ContDiff ℝ 1 g) (hgg : HasExpGrowth g) (hgd : HasExpGrowth (deriv g)) (x : ℝ) :
    Tendsto (fun p : ℝ × ℝ => deriv (potentialHeatSolution ν q g p.1) p.2)
      (𝓝[Icc 0 T ×ˢ univ] (0,x)) (𝓝 (deriv g x)) := by
  have h := potentialHeatSolution_deriv_continuousOn_of_contDiff hν hT hq hQ hqb hg hgg hgd
    (0,x) ⟨⟨le_rfl,hT⟩,mem_univ _⟩
  have he : potentialHeatSolution ν q g 0 = g := funext (potentialHeatSolution_initial ν q g)
  simpa only [he] using h.tendsto

end MathlibExt.Analysis.PDE.HeatKernel
