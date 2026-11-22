/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PDE.BurgersEvolution
public import MathlibExt.MeasureTheory.Integral.FirstMomentComparison
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Order preservation for the Burgers evolution

Bounded continuous ordered initial velocities produce ordered solutions for
positive viscosity. The proof compares Gaussian first moments, using the
monotonicity of the ratio of their initial heat profiles. Initial derivatives
and bounds on derivatives near zero are not required.

Reference: Gallay and Scheel, *Viscous shocks and long-time behavior of scalar
conservation laws*, Section 2,
https://www-fourier.univ-grenoble-alpes.fr/~gallay/ScalarCL.pdf.
-/

@[expose] public section

open MeasureTheory Set Real
open MathlibExt.Analysis MathlibExt.Analysis.GaussianMoments
open MathlibExt.Analysis.PDE.HeatKernel

namespace ColeHopf

/-- Ordered initial velocities give a monotone ratio of their positive heat profiles. -/
theorem initialHeatProfile_ratio_monotone {u v : ℝ → ℝ}
    (hu : Continuous u) (hv : Continuous v) {ν : ℝ} (hν : 0 < ν)
    (h : ∀ x, u x ≤ v x) (a : ℝ) :
    Monotone (fun x => initialHeatProfile ν u a x / initialHeatProfile ν v a x) := by
  let f := initialHeatProfile ν u a
  let g := initialHeatProfile ν v a
  have hd (x : ℝ) : HasDerivAt (fun y => f y / g y)
      ((v x - u x) * f x / (2 * ν * g x)) x := by
    convert (initialHeatProfile_hasDerivAt hu ν a x).div
      (initialHeatProfile_hasDerivAt hv ν a x) (initialHeatProfile_pos ν v a x).ne' using 1
    dsimp [f, g]
    field_simp
    ring
  exact monotone_of_hasDerivAt_nonneg hd (fun x =>
    div_nonneg (mul_nonneg (sub_nonneg.mpr (h x)) (initialHeatProfile_pos ν u a x).le)
      (mul_pos (mul_pos (by norm_num) hν) (initialHeatProfile_pos ν v a x)).le)

private theorem moment_comparison {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hbf : HasExpGrowth f) (hbg : HasExpGrowth g)
    (hpg : ∀ x, 0 < g x) (hm : Monotone (fun x => f x / g x))
    {p : ℝ × ℝ} (hp : 0 < p.1) :
    gaussianMoment f 0 p * gaussianMoment g 1 p ≤
      gaussianMoment f 1 p * gaussianMoment g 0 p := by
  let w := fun y => exp (-p.1 * y ^ 2 + p.2 * y)
  have hfi : Integrable (fun y => w y * f y) := by
    simpa only [pow_zero, one_mul] using
      integrable_gaussianMoment_of_exp_growth hf.aestronglyMeasurable hbf 0 hp
  have hgi : Integrable (fun y => w y * g y) := by
    simpa only [pow_zero, one_mul] using
      integrable_gaussianMoment_of_exp_growth hg.aestronglyMeasurable hbg 0 hp
  have hyf : Integrable (fun y => y * (w y * f y)) := by
    simpa only [pow_one, mul_assoc] using
      integrable_gaussianMoment_of_exp_growth hf.aestronglyMeasurable hbf 1 hp
  have hyg : Integrable (fun y => y * (w y * g y)) := by
    simpa only [pow_one, mul_assoc] using
      integrable_gaussianMoment_of_exp_growth hg.aestronglyMeasurable hbg 1 hp
  have hh := MathlibExt.MeasureTheory.firstMoment_mul_integral_le hfi hgi hyf hyg
    (fun y z => ?_)
  · simpa only [gaussianMoment, pow_zero, pow_one, one_mul, mul_assoc] using hh
  · have hc : 0 ≤ (y - z) * (f y * g z - f z * g y) := by
      rcases le_total z y with hzy | hyz
      · have hm' := (div_le_div_iff₀ (hpg z) (hpg y)).mp (hm hzy)
        exact mul_nonneg (sub_nonneg.mpr hzy) (sub_nonneg.mpr hm')
      · have hm' := (div_le_div_iff₀ (hpg y) (hpg z)).mp (hm hyz)
        exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hyz) (sub_nonpos.mpr hm')
    have hw : 0 < w y * w z := mul_pos (exp_pos _) (exp_pos _)
    nlinarith [mul_nonneg hw.le hc]

/-- Positive-time velocity in terms of the normalized first Gaussian moment. -/
theorem burgersSolution_eq_gaussianMoment {u : ℝ → ℝ} (hu : Continuous u)
    (hb : ∃ M, ∀ x, |u x| ≤ M) {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) (a x : ℝ) :
    burgersSolution ν u a t x = x / t -
      gaussianMoment (initialHeatProfile ν u a) 1 (1 / (4 * (ν * t)), x / (2 * (ν * t))) /
        (t * gaussianMoment (initialHeatProfile ν u a) 0
          (1 / (4 * (ν * t)), x / (2 * (ν * t)))) := by
  let f := initialHeatProfile ν u a
  have hf := (initialHeatProfile_contDiff hu ν a).continuous
  have hg := initialHeatProfile_hasExpGrowth hb hν a
  have htime := mul_pos hν ht
  have he : heatSolution f (ν * t) x = heatKernel ℝ (ν * t) x *
      gaussianMoment f 0 (1 / (4 * (ν * t)), x / (2 * (ν * t))) := by
    rw [heatSolution_eq_gaussianMoment f htime, heatKernel_real]
  have hp := heatSolution_pos_of_exp_growth hf hg (initialHeatProfile_pos ν u a) (ν * t) x
  have hk := heatKernel_pos htime x
  have hm : 0 < gaussianMoment f 0 (1 / (4 * (ν * t)), x / (2 * (ν * t))) := by
    rw [he] at hp
    exact (mul_pos_iff_of_pos_left hk).mp hp
  change -2 * ν * (deriv (heatSolution f (ν * t)) x / heatSolution f (ν * t) x) = _
  rw [(heatSolution_hasDerivAt_space_of_exp_growth hf.aestronglyMeasurable hg htime x).deriv, he]
  dsimp only [f] at *
  generalize h0 : gaussianMoment (initialHeatProfile ν u a) 0
    (1 / (4 * (ν * t)), x / (2 * (ν * t))) = m0 at *
  generalize h1 : gaussianMoment (initialHeatProfile ν u a) 1
    (1 / (4 * (ν * t)), x / (2 * (ν * t))) = m1 at *
  field_simp
  ring

/-- Burgers evolution preserves pointwise order for bounded continuous initial velocities. -/
theorem burgersSolution_mono {u v : ℝ → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hbu : ∃ M, ∀ x, |u x| ≤ M) (hbv : ∃ M, ∀ x, |v x| ≤ M)
    {ν : ℝ} (hν : 0 < ν) (h : ∀ x, u x ≤ v x) (a : ℝ)
    {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    burgersSolution ν u a t x ≤ burgersSolution ν v a t x := by
  rcases ht.eq_or_lt with ht | ht
  · subst t
    simpa only [burgersSolution_zero hu hν.ne', burgersSolution_zero hv hν.ne'] using h x
  let p : ℝ × ℝ := (1 / (4 * (ν * t)), x / (2 * (ν * t)))
  have hp : 0 < p.1 := by dsimp [p]; positivity
  have hm := moment_comparison (initialHeatProfile_contDiff hu ν a).continuous
    (initialHeatProfile_contDiff hv ν a).continuous (initialHeatProfile_hasExpGrowth hbu hν a)
    (initialHeatProfile_hasExpGrowth hbv hν a)
    (initialHeatProfile_pos ν v a) (initialHeatProfile_ratio_monotone hu hv hν h a) hp
  have hpos (w : ℝ → ℝ) (hw : Continuous w) (hbw : ∃ M, ∀ x, |w x| ≤ M) :
      0 < gaussianMoment (initialHeatProfile ν w a) 0 p := by
    have hh := heatSolution_pos_of_exp_growth (initialHeatProfile_contDiff hw ν a).continuous
      (initialHeatProfile_hasExpGrowth hbw hν a) (initialHeatProfile_pos ν w a) (ν * t) x
    rw [heatSolution_eq_gaussianMoment _ (mul_pos hν ht)] at hh
    exact (mul_pos_iff_of_pos_left (mul_pos (rpow_pos_of_pos (by positivity) _)
      (exp_pos _))).mp hh
  rw [burgersSolution_eq_gaussianMoment hu hbu hν ht,
    burgersSolution_eq_gaussianMoment hv hbv hν ht]
  apply sub_le_sub_left
  apply (div_le_div_iff₀ (mul_pos ht (hpos v hv hbv)) (mul_pos ht (hpos u hu hbu))).mpr
  nlinarith [mul_le_mul_of_nonneg_left hm ht.le]

/-- Comparison allows independent spatial normalization anchors. -/
theorem burgersSolution_mono_of_anchors {u v : ℝ → ℝ}
    (hu : Continuous u) (hv : Continuous v)
    (hbu : ∃ M, ∀ x, |u x| ≤ M) (hbv : ∃ M, ∀ x, |v x| ≤ M)
    {ν : ℝ} (hν : 0 < ν) (h : ∀ x, u x ≤ v x) (a b : ℝ)
    {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    burgersSolution ν u a t x ≤ burgersSolution ν v b t x := by
  rw [burgersSolution_anchor_independent hv hbv hν b a t x ht]
  exact burgersSolution_mono hu hv hbu hbv hν h a ht x

end ColeHopf
