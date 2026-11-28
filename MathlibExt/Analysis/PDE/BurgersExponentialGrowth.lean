/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PDE.BurgersInitialValue
public import MathlibExt.Analysis.PDE.HeatKernelExponentialGrowth
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Burgers initial data without a primitive-bound restriction

Every bounded continuous real velocity gives an anchored exponential heat profile
of at most exponential growth, as does its derivative. The existing heat-kernel
and Cole–Hopf formula therefore defines a classical positive-time Burgers solution
with exactly that pointwise initial trace, for every positive viscosity.

The solution formula is unchanged. In particular nonzero constant velocities and
bounded velocities with primitives unbounded below are now included. No uniqueness,
uniform-in-space convergence, or joint smoothness at time zero is asserted.

Reference: Gesztesy and Holden, *The Cole–Hopf and Miura transformations revisited*,
Theorem 3.3 and Remark 3.5, https://arxiv.org/abs/solv-int/9812025. Bounded continuous
velocity is a sufficient subclass of the source's broader growth setting.
-/

@[expose] public section

open MeasureTheory Set Filter Real
open scoped ContDiff Topology Interval
open MathlibExt.Analysis MathlibExt.Analysis.PDE.HeatKernel

namespace ColeHopf

/-- Bounded velocity yields at most exponential growth of its anchored heat profile. -/
theorem initialHeatProfile_hasExpGrowth {u₀ : ℝ → ℝ} (hb : ∃ M, ∀ x, |u₀ x| ≤ M)
    {ν : ℝ} (hν : 0 < ν) (x₀ : ℝ) : HasExpGrowth (initialHeatProfile ν u₀ x₀) := by
  obtain ⟨M, hM⟩ := hb
  have hM0 : 0 ≤ M := (abs_nonneg (u₀ 0)).trans (hM 0)
  let c := M / (2 * ν)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  refine ⟨exp (c * |x₀|), c, (exp_pos _).le, hc, fun x => ?_⟩
  rw [abs_of_pos (initialHeatProfile_pos ν u₀ x₀ x)]
  change exp (-(∫ y in x₀..x, u₀ y) / (2 * ν)) ≤ _
  rw [← exp_add]
  apply exp_le_exp.mpr
  have hi : |∫ y in x₀..x, u₀ y| ≤ M * |x - x₀| := by
    simpa only [Real.norm_eq_abs] using
      (intervalIntegral.norm_integral_le_of_norm_le_const (fun y _ =>
        show ‖u₀ y‖ ≤ M by simpa only [Real.norm_eq_abs] using hM y))
  calc
    _ ≤ |∫ y in x₀..x, u₀ y| / (2 * ν) :=
      div_le_div_of_nonneg_right (neg_le_abs _) (by positivity)
    _ ≤ (M * (|x| + |x₀|)) / (2 * ν) :=
      div_le_div_of_nonneg_right
        (hi.trans (mul_le_mul_of_nonneg_left (abs_sub x x₀) hM0)) (by positivity)
    _ = _ := by dsimp [c]; ring

/-- For a bounded continuous velocity and positive viscosity, the derivative of the anchored
profile has exponential growth as well. -/
theorem initialHeatProfile_deriv_hasExpGrowth {u₀ : ℝ → ℝ} (hu : Continuous u₀)
    (hb : ∃ M, ∀ x, |u₀ x| ≤ M) {ν : ℝ} (hν : 0 < ν) (x₀ : ℝ) :
    HasExpGrowth (deriv (initialHeatProfile ν u₀ x₀)) := by
  obtain ⟨P, c, hP, hc, hp⟩ := initialHeatProfile_hasExpGrowth hb hν x₀
  obtain ⟨M, hM⟩ := hb
  have hM0 : 0 ≤ M := (abs_nonneg (u₀ 0)).trans (hM 0)
  refine ⟨M / (2 * ν) * P, c, by positivity, hc, fun x => ?_⟩
  rw [(initialHeatProfile_hasDerivAt hu ν x₀ x).deriv, abs_mul, abs_div, abs_neg,
    abs_of_pos (by positivity : 0 < 2 * ν)]
  calc
    _ ≤ M / (2 * ν) * (P * exp (c * |x|)) :=
      mul_le_mul (div_le_div_of_nonneg_right (hM x) (by positivity)) (hp x)
        (abs_nonneg _) (by positivity)
    _ = _ := by ring

private theorem heatProfile_contDiffOn_growth {f : ℝ → ℝ} (hf : Continuous f)
    (hg : HasExpGrowth f) {ν : ℝ} (hν : 0 < ν) :
    ContDiffOn ℝ 3 (Function.uncurry (fun s y => heatSolution f (ν * s) y)) (Ioi 0 ×ˢ univ) := by
  change ContDiffOn ℝ 3 (fun p : ℝ × ℝ => heatSolution f (ν * p.1) p.2) (Ioi 0 ×ˢ univ)
  exact (heatSolution_contDiffOn_scaled_of_exp_growth hf.aestronglyMeasurable hg hν).of_le (by simp)

/-- Actual joint positive-time regularity for an exponentially growing positive profile. -/
theorem burgersFromHeat_contDiffOn_of_exp_growth {f : ℝ → ℝ} (hf : Continuous f)
    (hg : HasExpGrowth f) (hp : ∀ x, 0 < f x) {ν : ℝ} (hν : 0 < ν) :
    ContDiffOn ℝ 2 (Function.uncurry (burgersFromHeat ν f)) (Ioi 0 ×ˢ univ) :=
  OnInterval.classicalTransform_contDiffOn isOpen_Ioi isOpen_univ ν
    (fun s y => heatSolution f (ν * s) y) (heatProfile_contDiffOn_growth hf hg hν)
    (fun p _ => ne_of_gt (heatSolution_pos_of_exp_growth hf hg hp (ν * p.1) p.2))

/-- The Cole–Hopf field of a continuous, positive, exponentially growing profile solves Burgers
at every positive time, for positive viscosity. -/
theorem burgersFromHeat_burgers_of_exp_growth {f : ℝ → ℝ} (hf : Continuous f)
    (hg : HasExpGrowth f) (hp : ∀ x, 0 < f x) {ν : ℝ} (hν : 0 < ν)
    (t x : ℝ) (ht : 0 < t) :
    deriv (fun s => burgersFromHeat ν f s x) t +
      burgersFromHeat ν f t x * deriv (burgersFromHeat ν f t) x =
        ν * iteratedDeriv 2 (burgersFromHeat ν f t) x := by
  have hheat : ∀ᶠ y in 𝓝 x, deriv (fun s => heatSolution f (ν * s) y) t =
      ν * iteratedDeriv 2 (heatSolution f (ν * t)) y := by
    filter_upwards with y
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      (heatSolution_hasDerivAt_time_scaled_of_exp_growth hf.aestronglyMeasurable hg hν ht y).deriv
  exact OnInterval.classicalTransform_burgers isOpen_Ioi isOpen_univ ν
    (fun s y => heatSolution f (ν * s) y) (heatProfile_contDiffOn_growth hf hg hν)
    t x ht (mem_univ x) (ne_of_gt (heatSolution_pos_of_exp_growth hf hg hp (ν * t) x)) hheat

/-- Pointwise initial logarithmic-derivative recovery for exponential growth. -/
theorem burgersFromHeat_tendsto_zero_of_exp_growth {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hg : HasExpGrowth f) (hdg : HasExpGrowth (deriv f)) {ν : ℝ} (hν : 0 < ν)
    (x : ℝ) (hx : f x ≠ 0) :
    Tendsto (fun t => burgersFromHeat ν f t x) (𝓝[>] 0) (𝓝 (-2 * ν * (deriv f x / f x))) :=
  tendsto_const_nhds.mul
    ((heatSolution_deriv_tendsto_zero_scaled_of_exp_growth hf hg hdg hν x).div
      (heatSolution_tendsto_zero_scaled_of_exp_growth hf.continuous hg hν x) hx)

/-- Every bounded continuous initial velocity is recovered, without a primitive bound. -/
theorem burgersSolution_tendsto_zero_of_bounded {u₀ : ℝ → ℝ} (hu : Continuous u₀)
    (hb : ∃ M, ∀ x, |u₀ x| ≤ M) {ν : ℝ} (hν : 0 < ν) (x₀ x : ℝ) :
    Tendsto (fun t => burgersSolution ν u₀ x₀ t x) (𝓝[>] 0) (𝓝 (u₀ x)) := by
  have h := burgersFromHeat_tendsto_zero_of_exp_growth (initialHeatProfile_contDiff hu ν x₀)
    (initialHeatProfile_hasExpGrowth hb hν x₀) (initialHeatProfile_deriv_hasExpGrowth hu hb hν x₀)
    hν x (ne_of_gt (initialHeatProfile_pos ν u₀ x₀ x))
  simpa only [burgersSolution, initialHeatProfile_recovery hu hν.ne' x₀ x] using h

/-- Every bounded continuous velocity yields a jointly `C²` positive-time solution. -/
theorem burgersSolution_contDiffOn_of_bounded {u₀ : ℝ → ℝ} (hu : Continuous u₀)
    (hb : ∃ M, ∀ x, |u₀ x| ≤ M) {ν : ℝ} (hν : 0 < ν) (x₀ : ℝ) :
    ContDiffOn ℝ 2 (Function.uncurry (burgersSolution ν u₀ x₀)) (Ioi 0 ×ˢ univ) :=
  burgersFromHeat_contDiffOn_of_exp_growth (initialHeatProfile_contDiff hu ν x₀).continuous
    (initialHeatProfile_hasExpGrowth hb hν x₀) (initialHeatProfile_pos ν u₀ x₀) hν

/-- Every bounded continuous velocity yields a classical positive-time Burgers solution. -/
theorem burgersSolution_burgers_of_bounded {u₀ : ℝ → ℝ} (hu : Continuous u₀)
    (hb : ∃ M, ∀ x, |u₀ x| ≤ M) {ν : ℝ} (hν : 0 < ν) (x₀ t x : ℝ) (ht : 0 < t) :
    deriv (fun s => burgersSolution ν u₀ x₀ s x) t +
      burgersSolution ν u₀ x₀ t x * deriv (burgersSolution ν u₀ x₀ t) x =
        ν * iteratedDeriv 2 (burgersSolution ν u₀ x₀ t) x :=
  burgersFromHeat_burgers_of_exp_growth (initialHeatProfile_contDiff hu ν x₀).continuous
    (initialHeatProfile_hasExpGrowth hb hν x₀) (initialHeatProfile_pos ν u₀ x₀) hν t x ht

/-- Classical existence and pointwise initial recovery for every bounded continuous
real velocity and positive viscosity, using the existing explicit solution formula. -/
theorem burgersSolution_solves_initial_value_of_bounded {u₀ : ℝ → ℝ} (hu : Continuous u₀)
    (hb : ∃ M, ∀ x, |u₀ x| ≤ M) {ν : ℝ} (hν : 0 < ν) (x₀ : ℝ) :
    ContDiffOn ℝ 2 (Function.uncurry (burgersSolution ν u₀ x₀)) (Ioi 0 ×ˢ univ) ∧
    (∀ t, 0 < t → ∀ x,
      deriv (fun s => burgersSolution ν u₀ x₀ s x) t +
        burgersSolution ν u₀ x₀ t x * deriv (burgersSolution ν u₀ x₀ t) x =
          ν * iteratedDeriv 2 (burgersSolution ν u₀ x₀ t) x) ∧
    (∀ x, Tendsto (fun t => burgersSolution ν u₀ x₀ t x) (𝓝[>] 0) (𝓝 (u₀ x))) :=
  ⟨burgersSolution_contDiffOn_of_bounded hu hb hν x₀,
    fun t ht x => burgersSolution_burgers_of_bounded hu hb hν x₀ t x ht,
    burgersSolution_tendsto_zero_of_bounded hu hb hν x₀⟩

end ColeHopf
