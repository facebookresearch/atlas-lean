/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Analysis.PDE.PotentialHeatComparison
import MathlibExt.Analysis.PDE.HeatKernelUniqueness
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Positive potential-heat evolution and free-heat bounds

For nonnegative continuous exponential-growth data and a potential bounded in
absolute value by `Q`, the actual Volterra solution lies between free heat
multiplied by `exp (-Q*t)` and by `exp (Q*t)`. In particular, pointwise strictly
positive initial data give a strictly positive solution, with no uniform positive
lower bound or initial derivative. Initial-data order is preserved even for
signed data with different growth exponents.

The proof uses the whole-line potential comparison theorem. Only the freely
evolved datum is assumed nonnegative; positivity of the actual solution is a
conclusion. Finite spatial C2 potential regularity with bounded continuous jets
suffices. No potential time derivative is required.

Reference: James Nolen, *Partial Differential Equations and Diffusion Processes*,
section 2.8, https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf,
for the zeroth-order maximum-principle background. The weighted whole-line bounds
are derived from the established Gaussian and potential-comparison theorems.
-/

@[expose] public section

open Set Real
open scoped ContDiff
open MathlibExt.Analysis MathlibExt.Analysis.PDE.HeatWholeLine

namespace MathlibExt.Analysis.PDE.HeatKernel

private theorem weighted_heat_continuous {g : ℝ → ℝ} (hg : Continuous g)
    (hgg : HasExpGrowth g) (ν a : ℝ) :
    Continuous (fun p : ℝ × ℝ => exp (a*p.1) * heatSolution g (ν*p.1) p.2) :=
  (continuous_exp.comp (continuous_const.mul continuous_fst)).mul
    ((heatSolution_continuous_of_exp_growth hg hgg).comp
      ((continuous_const.mul continuous_fst).prodMk continuous_snd))

private theorem weighted_heat_contDiff {g : ℝ → ℝ} (hg : Continuous g)
    (hgg : HasExpGrowth g) {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) (a x : ℝ) :
    ContDiffAt ℝ 2 (fun y => exp (a*t) * heatSolution g (ν*t) y) x := by
  have hj : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => heatSolution g (ν*p.1) p.2) (t,x) :=
    (heatSolution_contDiffOn_scaled_of_exp_growth hg.aestronglyMeasurable hgg hν).contDiffAt
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨ht, mem_univ x⟩)
  exact contDiffAt_const.mul ((hj.of_le (by simp)).comp x
    (contDiffAt_const.prodMk contDiffAt_id))

private theorem weighted_heat_time {g : ℝ → ℝ} (hg : Continuous g)
    (hgg : HasExpGrowth g) {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) (a x : ℝ) :
    HasDerivAt (fun s => exp (a*s) * heatSolution g (ν*s) x)
      (exp (a*t) * (a*heatSolution g (ν*t) x +
        ν*iteratedDeriv 2 (heatSolution g (ν*t)) x)) t := by
  have hh := heatSolution_hasDerivAt_time_scaled_of_exp_growth hg.aestronglyMeasurable hgg hν ht x
  convert (((hasDerivAt_id' t).const_mul a).exp.mul hh) using 1
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  ring

private theorem weighted_heat_second (g : ℝ → ℝ) (ν a t x : ℝ) :
    iteratedDeriv 2 (fun y => exp (a*t)*heatSolution g (ν*t) y) x =
      exp (a*t)*iteratedDeriv 2 (heatSolution g (ν*t)) x := by
  rw [iteratedDeriv_const_mul_field]

private theorem weighted_heat_growth {g : ℝ → ℝ} (hg : Continuous g)
    (hgg : HasExpGrowth g) {ν : ℝ} (hν : 0 ≤ ν) (a T : ℝ) :
    HasExpGrowthOnStrip (fun t x => exp (a*t)*heatSolution g (ν*t) x) T := by
  obtain ⟨M,c,hM,hc,hb⟩ := heatSolution_hasExpGrowthOnStrip hg hgg hν T
  refine ⟨exp (|a| * |T|)*M,c,by positivity,hc,fun t ht x => ?_⟩
  have he : exp (a*t) ≤ exp (|a| * |T|) := exp_le_exp.mpr
    ((mul_le_mul_of_nonneg_right (le_abs_self a) ht.1).trans
      (mul_le_mul_of_nonneg_left (ht.2.trans (le_abs_self T)) (abs_nonneg a)))
  rw [abs_mul,abs_of_pos (exp_pos _)]
  calc
    exp (a*t)*|heatSolution g (ν*t) x| ≤ exp (|a| * |T|)*(M*exp (c*|x|)) :=
      mul_le_mul he (hb t ht x) (abs_nonneg _) (exp_pos _).le
    _ = _ := by ring

/-- Nonnegative initial data give quantitative free-heat lower and upper bounds
for the actual potential-heat solution when `|q| ≤ Q`. Both time endpoints are included. -/
theorem potentialHeatSolution_heat_bounds
    {q : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {ν T t Q : ℝ}
    (hν : 0 < ν) (hqs : ∀ s ∈ Icc 0 T, ContDiff ℝ 2 (q s))
    (hqc : ∀ k ≤ 2, ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv k (q p.1) p.2)
      (Icc 0 T ×ˢ univ))
    (hqb : ∀ k ≤ 2, ∃ M, ∀ s ∈ Icc 0 T, ∀ x, |iteratedDeriv k (q s) x| ≤ M)
    (hQ : 0 ≤ Q) (hQb : ∀ s ∈ Icc 0 T, ∀ x, |q s x| ≤ Q)
    (hg : Continuous g) (hgg : HasExpGrowth g) (hgp : ∀ x, 0 ≤ g x)
    (ht : t ∈ Icc 0 T) (x : ℝ) :
    exp (-Q*t)*heatSolution g (ν*t) x ≤ potentialHeatSolution ν q g t x ∧
      potentialHeatSolution ν q g t x ≤ exp (Q*t)*heatSolution g (ν*t) x := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hq : ContinuousOn (Function.uncurry q) (Icc 0 T ×ˢ univ) := by
    simpa only [iteratedDeriv_zero, Function.uncurry_def] using hqc 0 (by omega)
  have hc := potentialHeatSolution_continuousOn hν.le hT hq hQ hQb hg hgg
  have hx (s : ℝ) (hs : s ∈ Ioo 0 T) (y : ℝ) :
      ContDiffAt ℝ 2 (potentialHeatSolution ν q g s) y :=
    (potentialHeatSolution_contDiff_space (n := 2) hν hqs hqc hqb hg hgg ⟨hs.1,hs.2.le⟩).contDiffAt
  let pt := fun s y => ν*iteratedDeriv 2 (potentialHeatSolution ν q g s) y +
    q s y*potentialHeatSolution ν q g s y
  have hpt (s : ℝ) (hs : s ∈ Ioo 0 T) (y : ℝ) :
      HasDerivAt (fun r => potentialHeatSolution ν q g r y) (pt s y) s := by
    simpa only [pt, iteratedDeriv_succ, iteratedDeriv_zero] using
      potentialHeatSolution_hasDerivAt_time hν hqs hqc hqb hg hgg hs y
  have hpg := potentialHeatSolution_hasExpGrowthOnStrip hν.le hq hQ hQb hg hgg
  have hqu (s : ℝ) (hs : s ∈ Ioo 0 T) (y : ℝ) : q s y ≤ Q :=
    (le_abs_self _).trans (hQb s ⟨hs.1.le,hs.2.le⟩ y)
  constructor
  · apply le_of_potential_residual_le
      (u := fun s y => exp (-Q*s)*heatSolution g (ν*s) y)
      (ut := fun s y => exp (-Q*s)*(-Q*heatSolution g (ν*s) y +
        ν*iteratedDeriv 2 (heatSolution g (ν*s)) y))
      (v := potentialHeatSolution ν q g) (vt := pt) (q := q) hν.le
      (weighted_heat_continuous hg hgg ν (-Q)).continuousOn hc
      (fun s hs y => weighted_heat_contDiff hg hgg hν hs.1 (-Q) y) hx
      (fun s hs y => weighted_heat_time hg hgg hν hs.1 (-Q) y) hpt
      (fun s hs y => ?_) hqu (weighted_heat_growth hg hgg hν.le (-Q) T) hpg
      (fun y => by simp) t ht x
    rw [weighted_heat_second]
    have hlow : -Q ≤ q s y := (abs_le.mp (hQb s ⟨hs.1.le,hs.2.le⟩ y)).1
    have hh := mul_nonneg (by linarith : 0 ≤ Q+q s y)
      (mul_nonneg (exp_pos (-Q*s)).le (heatSolution_nonneg hgp (ν*s) y))
    dsimp [pt]
    nlinarith
  · apply le_of_potential_residual_le
      (u := potentialHeatSolution ν q g) (ut := pt)
      (v := fun s y => exp (Q*s)*heatSolution g (ν*s) y)
      (vt := fun s y => exp (Q*s)*(Q*heatSolution g (ν*s) y +
        ν*iteratedDeriv 2 (heatSolution g (ν*s)) y)) (q := q) hν.le hc
      (weighted_heat_continuous hg hgg ν Q).continuousOn hx
      (fun s hs y => weighted_heat_contDiff hg hgg hν hs.1 Q y) hpt
      (fun s hs y => weighted_heat_time hg hgg hν hs.1 Q y)
      (fun s hs y => ?_) hqu hpg (weighted_heat_growth hg hgg hν.le Q T)
      (fun y => by simp) t ht x
    rw [weighted_heat_second]
    have hh := mul_nonneg (sub_nonneg.mpr (hqu s hs y))
      (mul_nonneg (exp_pos (Q*s)).le (heatSolution_nonneg hgp (ν*s) y))
    dsimp [pt]
    nlinarith

/-- Nonnegative continuous exponential-growth initial data give a nonnegative
actual potential-heat solution, even for signed potentials. -/
theorem potentialHeatSolution_nonneg
    {q : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {ν T t : ℝ}
    (hν : 0 < ν) (hqs : ∀ s ∈ Icc 0 T, ContDiff ℝ 2 (q s))
    (hqc : ∀ k ≤ 2, ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv k (q p.1) p.2)
      (Icc 0 T ×ˢ univ))
    (hqb : ∀ k ≤ 2, ∃ M, ∀ s ∈ Icc 0 T, ∀ x, |iteratedDeriv k (q s) x| ≤ M)
    (hg : Continuous g) (hgg : HasExpGrowth g) (hgp : ∀ x, 0 ≤ g x)
    (ht : t ∈ Icc 0 T) (x : ℝ) : 0 ≤ potentialHeatSolution ν q g t x := by
  obtain ⟨Q,hQb⟩ := hqb 0 (by omega)
  simp only [iteratedDeriv_zero] at hQb
  have hQ : 0 ≤ Q := (abs_nonneg _).trans (hQb t ht x)
  exact (mul_nonneg (exp_pos _).le (heatSolution_nonneg hgp (ν*t) x)).trans
    (potentialHeatSolution_heat_bounds hν hqs hqc hqb hQ hQb hg hgg hgp ht x).1

/-- Pointwise strictly positive continuous initial data give a strictly positive
actual potential-heat solution. No uniform positive lower bound or initial derivative
is assumed, and both initial and terminal times are included. -/
theorem potentialHeatSolution_pos
    {q : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {ν T t : ℝ}
    (hν : 0 < ν) (hqs : ∀ s ∈ Icc 0 T, ContDiff ℝ 2 (q s))
    (hqc : ∀ k ≤ 2, ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv k (q p.1) p.2)
      (Icc 0 T ×ˢ univ))
    (hqb : ∀ k ≤ 2, ∃ M, ∀ s ∈ Icc 0 T, ∀ x, |iteratedDeriv k (q s) x| ≤ M)
    (hg : Continuous g) (hgg : HasExpGrowth g) (hgp : ∀ x, 0 < g x)
    (ht : t ∈ Icc 0 T) (x : ℝ) : 0 < potentialHeatSolution ν q g t x := by
  obtain ⟨Q,hQb⟩ := hqb 0 (by omega)
  simp only [iteratedDeriv_zero] at hQb
  have hQ : 0 ≤ Q := (abs_nonneg _).trans (hQb t ht x)
  exact (mul_pos (exp_pos _) (heatSolution_pos_of_exp_growth hg hgg hgp (ν*t) x)).trans_le
    (potentialHeatSolution_heat_bounds hν hqs hqc hqb hQ hQb hg hgg
      (fun y => (hgp y).le) ht x).1

/-- Ordered initial data give ordered actual potential-heat solutions. Both data
may change sign and may have different exponential growth rates. -/
theorem potentialHeatSolution_mono_initial
    {q : ℝ → ℝ → ℝ} {f g : ℝ → ℝ} {ν T t : ℝ}
    (hν : 0 < ν) (hqs : ∀ s ∈ Icc 0 T, ContDiff ℝ 2 (q s))
    (hqc : ∀ k ≤ 2, ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv k (q p.1) p.2)
      (Icc 0 T ×ˢ univ))
    (hqb : ∀ k ≤ 2, ∃ M, ∀ s ∈ Icc 0 T, ∀ x, |iteratedDeriv k (q s) x| ≤ M)
    (hf : Continuous f) (hfg : HasExpGrowth f) (hg : Continuous g) (hgg : HasExpGrowth g)
    (hfg_le : ∀ x, f x ≤ g x) (ht : t ∈ Icc 0 T) (x : ℝ) :
    potentialHeatSolution ν q f t x ≤ potentialHeatSolution ν q g t x := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hq : ContinuousOn (Function.uncurry q) (Icc 0 T ×ˢ univ) := by
    simpa only [iteratedDeriv_zero, Function.uncurry_def] using hqc 0 (by omega)
  obtain ⟨Q,hQb⟩ := hqb 0 (by omega)
  simp only [iteratedDeriv_zero] at hQb
  have hQ : 0 ≤ Q := (abs_nonneg _).trans (hQb t ht x)
  apply le_of_potential_residual_le
    (u := potentialHeatSolution ν q f) (v := potentialHeatSolution ν q g)
    (ut := fun s y => ν*iteratedDeriv 2 (potentialHeatSolution ν q f s) y +
      q s y*potentialHeatSolution ν q f s y)
    (vt := fun s y => ν*iteratedDeriv 2 (potentialHeatSolution ν q g s) y +
      q s y*potentialHeatSolution ν q g s y) (q := q) hν.le
    (potentialHeatSolution_continuousOn hν.le hT hq hQ hQb hf hfg)
    (potentialHeatSolution_continuousOn hν.le hT hq hQ hQb hg hgg)
    (fun s hs y => (potentialHeatSolution_contDiff_space (n := 2) hν hqs hqc hqb hf hfg
      ⟨hs.1,hs.2.le⟩).contDiffAt)
    (fun s hs y => (potentialHeatSolution_contDiff_space (n := 2) hν hqs hqc hqb hg hgg
      ⟨hs.1,hs.2.le⟩).contDiffAt)
    (fun s hs y => by
      simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using
        potentialHeatSolution_hasDerivAt_time hν hqs hqc hqb hf hfg hs y)
    (fun s hs y => by
      simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using
        potentialHeatSolution_hasDerivAt_time hν hqs hqc hqb hg hgg hs y)
    (fun _ _ _ => by ring_nf; rfl)
    (fun s hs y => (le_abs_self _).trans (hQb s ⟨hs.1.le,hs.2.le⟩ y))
    (potentialHeatSolution_hasExpGrowthOnStrip hν.le hq hQ hQb hf hfg)
    (potentialHeatSolution_hasExpGrowthOnStrip hν.le hq hQ hQb hg hgg)
    (fun y => by simpa only [potentialHeatSolution_initial] using hfg_le y) t ht x

end MathlibExt.Analysis.PDE.HeatKernel
