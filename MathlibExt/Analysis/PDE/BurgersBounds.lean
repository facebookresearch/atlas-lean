/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PDE.BurgersExponentialGrowth
public import MathlibExt.Analysis.PDE.HeatKernelContinuity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-!
# Burgers initial-range preservation and joint initial continuity

The existing Cole–Hopf solution for bounded continuous velocity is a positive
Gaussian-weighted average of its initial values. Consequently every initial
interval bound is preserved, with no bounded-primitive hypothesis. The solution
is jointly continuous up to initial time, even for nondifferentiable continuous
initial velocity.

All-real-time bounds and continuity include the existing stationary extension at
nonpositive times; the Burgers equation is asserted only at positive times in
`BurgersExponentialGrowth`. This is neither comparison between two arbitrary
solutions nor an IVP uniqueness theorem. No uniform-in-space initial convergence
or joint differentiability at time zero is asserted.

References: Gallay and Scheel, *Viscous shocks and long-time behavior of scalar
conservation laws*, Section 2 (range bounds),
https://www-fourier.univ-grenoble-alpes.fr/~gallay/ScalarCL.pdf;
Gesztesy and Holden, *The Cole–Hopf and Miura transformations revisited*, Theorem
3.3 and Remark 3.5 (the transform and growth setting),
https://arxiv.org/abs/solv-int/9812025. Here the initial data are continuous and
bounded, and the viscosity is any positive real number.
-/

@[expose] public section

open MeasureTheory Set Filter Real
open scoped ContDiff Topology
open MathlibExt.Analysis MathlibExt.Analysis.PDE.HeatKernel

namespace ColeHopf

private theorem weighted_profile_growth {u₀ : ℝ → ℝ}
    (hb : ∃ M, ∀ x, |u₀ x| ≤ M) {ν : ℝ} (hν : 0 < ν) (x₀ : ℝ) :
    HasExpGrowth (fun y => u₀ y * initialHeatProfile ν u₀ x₀ y) := by
  obtain ⟨A, c, hA, hc, h⟩ := initialHeatProfile_hasExpGrowth hb hν x₀
  obtain ⟨M, hM⟩ := hb
  have hM0 : 0 ≤ M := (abs_nonneg (u₀ 0)).trans (hM 0)
  refine ⟨M * A, c, mul_nonneg hM0 hA, hc, fun y => ?_⟩
  rw [abs_mul, mul_assoc]
  exact mul_le_mul (hM y) (h y) (abs_nonneg _) hM0

/-- The velocity is the heat average of the initial velocity weighted by its positive profile. -/
theorem burgersSolution_eq_weighted_heat {u₀ : ℝ → ℝ} (hu : Continuous u₀)
    (hb : ∃ M, ∀ x, |u₀ x| ≤ M) {ν : ℝ} (hν : 0 < ν) (x₀ t x : ℝ) :
    burgersSolution ν u₀ x₀ t x =
      heatSolution (fun y => u₀ y * initialHeatProfile ν u₀ x₀ y) (ν * t) x /
        heatSolution (initialHeatProfile ν u₀ x₀) (ν * t) x := by
  let f := initialHeatProfile ν u₀ x₀
  have hd : deriv f = fun y => (-1 / (2 * ν)) * (u₀ y * f y) := by
    funext y
    rw [(initialHeatProfile_hasDerivAt hu ν x₀ y).deriv]
    dsimp [f]
    ring
  change -2 * ν * (deriv (heatSolution f (ν * t)) x / heatSolution f (ν * t) x) = _
  rw [(heatSolution_hasDerivAt_deriv_of_exp_growth (initialHeatProfile_contDiff hu ν x₀)
    (initialHeatProfile_hasExpGrowth hb hν x₀)
    (initialHeatProfile_deriv_hasExpGrowth hu hb hν x₀) (ν * t) x).deriv,
    hd, heatSolution_const_mul]
  field_simp
  ring

/-- Every closed interval containing the initial velocity contains the constructed solution. -/
theorem burgersSolution_mem_Icc {u₀ : ℝ → ℝ} (hu : Continuous u₀) {a b ν : ℝ}
    (hν : 0 < ν) (h : ∀ x, u₀ x ∈ Icc a b) (x₀ t x : ℝ) :
    burgersSolution ν u₀ x₀ t x ∈ Icc a b := by
  have hb : ∃ M, ∀ x, |u₀ x| ≤ M := ⟨max |a| |b|, fun x => abs_le.mpr
    ⟨(neg_le_neg (le_max_left |a| |b|)).trans ((neg_abs_le a).trans (h x).1),
      (h x).2.trans ((le_abs_self b).trans (le_max_right |a| |b|))⟩⟩
  let f := initialHeatProfile ν u₀ x₀
  have hf : Continuous f := (initialHeatProfile_contDiff hu ν x₀).continuous
  have hg : HasExpGrowth f := initialHeatProfile_hasExpGrowth hb hν x₀
  have hw := weighted_profile_growth hb hν x₀
  have hp : 0 < heatSolution f (ν * t) x :=
    heatSolution_pos_of_exp_growth hf hg (initialHeatProfile_pos ν u₀ x₀) (ν * t) x
  rw [burgersSolution_eq_weighted_heat hu hb hν x₀ t x]
  constructor
  · apply (le_div_iff₀ hp).mpr
    have hl := heatSolution_mono_of_exp_growth
      (continuous_const.mul hf).aestronglyMeasurable (hu.mul hf).aestronglyMeasurable
      (hg.const_mul a) hw
      (fun y => mul_le_mul_of_nonneg_right (h y).1 (initialHeatProfile_pos ν u₀ x₀ y).le)
      (ν * t) x
    change heatSolution (fun y => a * f y) (ν * t) x ≤
      heatSolution (fun y => u₀ y * f y) (ν * t) x at hl
    simpa only [heatSolution_const_mul] using hl
  · apply (div_le_iff₀ hp).mpr
    have hr := heatSolution_mono_of_exp_growth
      (hu.mul hf).aestronglyMeasurable (continuous_const.mul hf).aestronglyMeasurable
      hw (hg.const_mul b)
      (fun y => mul_le_mul_of_nonneg_right (h y).2 (initialHeatProfile_pos ν u₀ x₀ y).le)
      (ν * t) x
    change heatSolution (fun y => u₀ y * f y) (ν * t) x ≤
      heatSolution (fun y => b * f y) (ν * t) x at hr
    simpa only [heatSolution_const_mul] using hr

/-- The initial uniform absolute bound is preserved at all nonnegative times
(and by the stationary extension at negative times). -/
theorem abs_burgersSolution_le {u₀ : ℝ → ℝ} (hu : Continuous u₀) {M ν : ℝ}
    (hν : 0 < ν) (hb : ∀ x, |u₀ x| ≤ M) (x₀ t x : ℝ) :
    |burgersSolution ν u₀ x₀ t x| ≤ M :=
  abs_le.mpr (burgersSolution_mem_Icc hu hν (fun x => abs_le.mp (hb x)) x₀ t x)

/-- Positive `C¹` profiles with exponentially growing derivative give joint continuity
of the Cole–Hopf field. Continuity allows any scaling `ν`; the heat profile is
stationary where `ν * t ≤ 0`. No Burgers PDE is asserted for nonpositive viscosity. -/
theorem burgersFromHeat_continuous_of_exp_growth {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hg : HasExpGrowth f) (hdg : HasExpGrowth (deriv f)) (hp : ∀ x, 0 < f x)
    (ν : ℝ) : Continuous (Function.uncurry (burgersFromHeat ν f)) := by
  have hs : Continuous (fun p : ℝ × ℝ => (ν * p.1, p.2)) := by fun_prop
  exact continuous_const.mul
    (((heatSolution_deriv_continuous_of_exp_growth hf hg hdg).comp hs).div
      ((heatSolution_continuous_of_exp_growth hf.continuous hg).comp hs)
      (fun p => ne_of_gt (heatSolution_pos_of_exp_growth hf.continuous hg hp (ν * p.1) p.2)))

/-- Bounded continuous initial velocity yields a jointly continuous solution up to time zero.
The all-real-time statement includes the stationary extension at negative times. -/
theorem burgersSolution_continuous_of_bounded {u₀ : ℝ → ℝ} (hu : Continuous u₀)
    (hb : ∃ M, ∀ x, |u₀ x| ≤ M) {ν : ℝ} (hν : 0 < ν) (x₀ : ℝ) :
    Continuous (Function.uncurry (burgersSolution ν u₀ x₀)) :=
  burgersFromHeat_continuous_of_exp_growth (initialHeatProfile_contDiff hu ν x₀)
    (initialHeatProfile_hasExpGrowth hb hν x₀) (initialHeatProfile_deriv_hasExpGrowth hu hb hν x₀)
    (initialHeatProfile_pos ν u₀ x₀) ν

/-- Initial recovery permits space and time to approach the boundary together. -/
theorem burgersSolution_tendsto_initial_of_bounded {u₀ : ℝ → ℝ} (hu : Continuous u₀)
    (hb : ∃ M, ∀ x, |u₀ x| ≤ M) {ν : ℝ} (hν : 0 < ν) (x₀ x : ℝ) :
    Tendsto (Function.uncurry (burgersSolution ν u₀ x₀)) (𝓝 (0, x)) (𝓝 (u₀ x)) := by
  simpa only [Function.uncurry_def, burgersSolution_zero hu hν.ne' x₀ x] using
    (burgersSolution_continuous_of_bounded hu hb hν x₀).tendsto (0, x)

end ColeHopf
