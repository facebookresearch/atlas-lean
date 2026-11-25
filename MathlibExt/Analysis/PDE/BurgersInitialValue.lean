/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PDE.HeatKernelDerivative
public import MathlibExt.Analysis.PDE.HeatKernelSmoothness
public import MathlibExt.Analysis.PDE.LocalColeHopf
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Recovering Burgers initial data by heat evolution

A positive bounded `C¹` heat profile with bounded derivative produces a classical
positive-time Burgers solution whose pointwise initial trace is `-2ν f'/f`.
For prescribed bounded continuous velocity `u₀`, the anchored exponential profile
`exp (-(∫ x₀..x, u₀)/(2ν))` recovers exactly `u₀`. A lower bound on the anchored
primitive is a sufficient condition for this profile and its derivative to stay
bounded, so the existing bounded-data heat construction applies.

This is an initial-value existence and pointwise recovery result for that stated
class. Arbitrary bounded velocities can have unbounded exponential profiles
(nonzero constant velocities already do); they require further growth estimates.
No uniqueness, uniform-in-space initial convergence or joint time-zero smoothness
is claimed. Positive viscosity is required for the heat evolution.

References: the heat initial-value argument in M. Schmidt, *Partial Differential
Equations*, HWS 2025, Chapter 4, Theorem 4.3,
https://www.wim.uni-mannheim.de/media/Lehrstuehle/wim/schmidt/HWS2025/chapter_4.pdf;
and the classical transformation in Gesztesy and Holden, *The Cole–Hopf and Miura
transformations revisited*, Theorem 3.3 and Remark 3.5,
https://arxiv.org/abs/solv-int/9812025.
The initial-trace assertion combines the derivative heat trace with this quotient.
-/

@[expose] public section

open MeasureTheory Set Filter Real
open scoped ContDiff Topology Interval
open MathlibExt.Analysis.PDE.HeatKernel

namespace ColeHopf

/-- Burgers evolution obtained from an initial heat profile `f`, with heat time
scaled by the viscosity. The profile must satisfy the hypotheses of the theorems below. -/
noncomputable def burgersFromHeat (ν : ℝ) (f : ℝ → ℝ) (t x : ℝ) : ℝ :=
  classicalTransform ν (fun s y => heatSolution f (ν * s) y) t x

private theorem heatProfile_contDiffOn {f : ℝ → ℝ} (hf : Continuous f)
    (hb : ∃ M, ∀ x, |f x| ≤ M) {ν : ℝ} (hν : 0 < ν) :
    ContDiffOn ℝ 3 (Function.uncurry (fun s y => heatSolution f (ν * s) y)) (Ioi 0 ×ˢ univ) := by
  change ContDiffOn ℝ 3 (fun p : ℝ × ℝ => heatSolution f (ν * p.1) p.2) (Ioi 0 ×ˢ univ)
  exact (heatSolution_contDiffOn_scaled hf.aestronglyMeasurable hb hν).of_le (by simp)

/-- Actual joint regularity of the constructed Burgers field on positive time. -/
theorem burgersFromHeat_contDiffOn {f : ℝ → ℝ} (hf : Continuous f)
    (hb : ∃ M, ∀ x, |f x| ≤ M) (hp : ∀ x, 0 < f x) {ν : ℝ} (hν : 0 < ν) :
    ContDiffOn ℝ 2 (Function.uncurry (burgersFromHeat ν f)) (Ioi 0 ×ˢ univ) :=
  OnInterval.classicalTransform_contDiffOn isOpen_Ioi isOpen_univ ν
    (fun s y => heatSolution f (ν * s) y) (heatProfile_contDiffOn hf hb hν)
    (fun p _ => ne_of_gt (heatSolution_pos hf hb hp (ν * p.1) p.2))

/-- The transformed heat evolution solves the viscous Burgers equation at every
positive-time point; its derivative existence follows from joint `C²` regularity. -/
theorem burgersFromHeat_burgers {f : ℝ → ℝ} (hf : Continuous f)
    (hb : ∃ M, ∀ x, |f x| ≤ M) (hp : ∀ x, 0 < f x) {ν : ℝ} (hν : 0 < ν)
    (t x : ℝ) (ht : 0 < t) :
    deriv (fun s => burgersFromHeat ν f s x) t +
      burgersFromHeat ν f t x * deriv (burgersFromHeat ν f t) x =
        ν * iteratedDeriv 2 (burgersFromHeat ν f t) x := by
  have hheat : ∀ᶠ y in 𝓝 x, deriv (fun s => heatSolution f (ν * s) y) t =
      ν * iteratedDeriv 2 (heatSolution f (ν * t)) y := by
    filter_upwards with y
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      (heatSolution_hasDerivAt_time_scaled hf hb hν ht y).deriv
  exact OnInterval.classicalTransform_burgers isOpen_Ioi isOpen_univ ν
    (fun s y => heatSolution f (ν * s) y) (heatProfile_contDiffOn hf hb hν)
    t x ht (mem_univ x) (ne_of_gt (heatSolution_pos hf hb hp (ν * t) x)) hheat

/-- Pointwise recovery of the initial logarithmic derivative. Nonvanishing is
needed only at the point where the trace is taken. -/
theorem burgersFromHeat_tendsto_zero {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hb : ∃ M, ∀ x, |f x| ≤ M) (hdb : ∃ M, ∀ x, |deriv f x| ≤ M)
    {ν : ℝ} (hν : 0 < ν) (x : ℝ) (hx : f x ≠ 0) :
    Tendsto (fun t => burgersFromHeat ν f t x) (𝓝[>] 0) (𝓝 (-2 * ν * (deriv f x / f x))) :=
  tendsto_const_nhds.mul ((heatSolution_deriv_tendsto_zero_scaled hf hb hdb hν x).div
    (heatSolution_tendsto_zero_scaled hf.continuous hb hν x) hx)

/-- The nonpositive-time convention also gives the prescribed quotient at time zero. -/
@[simp] theorem burgersFromHeat_zero (ν : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    burgersFromHeat ν f 0 x = -2 * ν * (deriv f x / f x) := by
  simp [burgersFromHeat, classicalTransform]

/-- Anchored exponential heat profile associated to prescribed Burgers data.
This is the spatial exponential in the initial slice of the inverse Cole–Hopf map. -/
noncomputable def initialHeatProfile (ν : ℝ) (u₀ : ℝ → ℝ) (x₀ x : ℝ) : ℝ :=
  exp (-(∫ y in x₀..x, u₀ y) / (2 * ν))

/-- The anchored exponential is strictly positive, with no uniform lower bound required. -/
theorem initialHeatProfile_pos (ν : ℝ) (u₀ : ℝ → ℝ) (x₀ x : ℝ) :
    0 < initialHeatProfile ν u₀ x₀ x := exp_pos _

/-- Normalization at the spatial anchor. -/
@[simp] theorem initialHeatProfile_anchor (ν : ℝ) (u₀ : ℝ → ℝ) (x₀ : ℝ) :
    initialHeatProfile ν u₀ x₀ x₀ = 1 := by simp [initialHeatProfile]

/-- The initial profile's actual derivative encodes the prescribed velocity. -/
theorem initialHeatProfile_hasDerivAt {u₀ : ℝ → ℝ} (hu : Continuous u₀) (ν x₀ x : ℝ) :
    HasDerivAt (initialHeatProfile ν u₀ x₀)
      (-u₀ x / (2 * ν) * initialHeatProfile ν u₀ x₀ x) x := by
  change HasDerivAt (fun z => exp (-(∫ y in x₀..z, u₀ y) / (2 * ν)))
    (-u₀ x / (2 * ν) * exp (-(∫ y in x₀..x, u₀ y) / (2 * ν))) x
  simpa only [Pi.neg_apply, mul_comm] using!
    (((hu.integral_hasStrictDerivAt x₀ x).hasDerivAt.neg).div_const (2 * ν)).exp

/-- Continuous data give a `C¹` initial heat profile. -/
theorem initialHeatProfile_contDiff {u₀ : ℝ → ℝ} (hu : Continuous u₀) (ν x₀ : ℝ) :
    ContDiff ℝ 1 (initialHeatProfile ν u₀ x₀) := by
  have hc : Continuous (initialHeatProfile ν u₀ x₀) := continuous_iff_continuousAt.mpr
    (fun x => (initialHeatProfile_hasDerivAt hu ν x₀ x).continuousAt)
  refine contDiff_one_iff_deriv.mpr ⟨fun x =>
    (initialHeatProfile_hasDerivAt hu ν x₀ x).differentiableAt, ?_⟩
  have he : deriv (initialHeatProfile ν u₀ x₀) =
      fun x => -u₀ x / (2 * ν) * initialHeatProfile ν u₀ x₀ x :=
    funext (fun x => (initialHeatProfile_hasDerivAt hu ν x₀ x).deriv)
  rw [he]
  exact (hu.neg.div_const (2 * ν)).mul hc

/-- A lower bound for the anchored primitive gives an upper bound for the heat profile. -/
theorem initialHeatProfile_bounded {u₀ : ℝ → ℝ} {ν x₀ : ℝ} (hν : 0 < ν)
    (hU : ∃ L, ∀ x, L ≤ ∫ y in x₀..x, u₀ y) :
    ∃ M, ∀ x, |initialHeatProfile ν u₀ x₀ x| ≤ M := by
  obtain ⟨L, hL⟩ := hU
  refine ⟨exp (-L / (2 * ν)), fun x => ?_⟩
  rw [abs_of_pos (initialHeatProfile_pos ν u₀ x₀ x)]
  exact exp_le_exp.mpr (div_le_div_of_nonneg_right (neg_le_neg (hL x)) (by positivity))

/-- Bounded prescribed data and a bounded exponential profile give a bounded profile derivative. -/
theorem initialHeatProfile_deriv_bounded {u₀ : ℝ → ℝ} (hu : Continuous u₀)
    (hb : ∃ M, ∀ x, |u₀ x| ≤ M) {ν x₀ : ℝ} (hν : 0 < ν)
    (hU : ∃ L, ∀ x, L ≤ ∫ y in x₀..x, u₀ y) :
    ∃ M, ∀ x, |deriv (initialHeatProfile ν u₀ x₀) x| ≤ M := by
  obtain ⟨M, hM⟩ := hb
  obtain ⟨P, hP⟩ := initialHeatProfile_bounded hν hU
  have hM0 : 0 ≤ M := (abs_nonneg (u₀ 0)).trans (hM 0)
  refine ⟨M / (2 * ν) * P, fun x => ?_⟩
  rw [(initialHeatProfile_hasDerivAt hu ν x₀ x).deriv, abs_mul, abs_div, abs_neg,
    abs_of_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hν)]
  exact mul_le_mul (div_le_div_of_nonneg_right (hM x) (by positivity)) (hP x)
    (abs_nonneg _) (by positivity)

/-- The initial logarithmic derivative is exactly the prescribed Burgers velocity. -/
theorem initialHeatProfile_recovery {u₀ : ℝ → ℝ} (hu : Continuous u₀) {ν : ℝ}
    (hν : ν ≠ 0) (x₀ x : ℝ) :
    -2 * ν * (deriv (initialHeatProfile ν u₀ x₀) x / initialHeatProfile ν u₀ x₀ x) = u₀ x := by
  rw [(initialHeatProfile_hasDerivAt hu ν x₀ x).deriv]
  have hp := ne_of_gt (initialHeatProfile_pos ν u₀ x₀ x)
  field_simp

/-- Explicit heat-kernel construction from prescribed Burgers initial data and a spatial anchor. -/
noncomputable def burgersSolution (ν : ℝ) (u₀ : ℝ → ℝ) (x₀ t x : ℝ) : ℝ :=
  burgersFromHeat ν (initialHeatProfile ν u₀ x₀) t x

/-- The constructed solution recovers the prescribed initial velocity pointwise. -/
theorem burgersSolution_tendsto_zero {u₀ : ℝ → ℝ} (hu : Continuous u₀)
    (hb : ∃ M, ∀ x, |u₀ x| ≤ M) {ν x₀ : ℝ} (hν : 0 < ν)
    (hU : ∃ L, ∀ x, L ≤ ∫ y in x₀..x, u₀ y) (x : ℝ) :
    Tendsto (fun t => burgersSolution ν u₀ x₀ t x) (𝓝[>] 0) (𝓝 (u₀ x)) := by
  have h := burgersFromHeat_tendsto_zero (initialHeatProfile_contDiff hu ν x₀)
    (initialHeatProfile_bounded hν hU) (initialHeatProfile_deriv_bounded hu hb hν hU)
    hν x (ne_of_gt (initialHeatProfile_pos ν u₀ x₀ x))
  simpa only [burgersSolution, initialHeatProfile_recovery hu hν.ne' x₀ x] using h

/-- The time-zero extension agrees exactly with the prescribed velocity. -/
@[simp] theorem burgersSolution_zero {u₀ : ℝ → ℝ} (hu : Continuous u₀) {ν : ℝ}
    (hν : ν ≠ 0) (x₀ x : ℝ) : burgersSolution ν u₀ x₀ 0 x = u₀ x := by
  exact (burgersFromHeat_zero ν (initialHeatProfile ν u₀ x₀) x).trans
    (initialHeatProfile_recovery hu hν x₀ x)

/-- The explicit initial-value solution has joint `C²` regularity at positive time. -/
theorem burgersSolution_contDiffOn {u₀ : ℝ → ℝ} (hu : Continuous u₀)
    {ν x₀ : ℝ} (hν : 0 < ν) (hU : ∃ L, ∀ x, L ≤ ∫ y in x₀..x, u₀ y) :
    ContDiffOn ℝ 2 (Function.uncurry (burgersSolution ν u₀ x₀)) (Ioi 0 ×ˢ univ) :=
  burgersFromHeat_contDiffOn (initialHeatProfile_contDiff hu ν x₀).continuous
    (initialHeatProfile_bounded hν hU) (initialHeatProfile_pos ν u₀ x₀) hν

/-- The explicit construction solves the viscous Burgers equation at positive time. -/
theorem burgersSolution_burgers {u₀ : ℝ → ℝ} (hu : Continuous u₀)
    {ν x₀ : ℝ} (hν : 0 < ν) (hU : ∃ L, ∀ x, L ≤ ∫ y in x₀..x, u₀ y)
    (t x : ℝ) (ht : 0 < t) :
    deriv (fun s => burgersSolution ν u₀ x₀ s x) t +
      burgersSolution ν u₀ x₀ t x * deriv (burgersSolution ν u₀ x₀ t) x =
        ν * iteratedDeriv 2 (burgersSolution ν u₀ x₀ t) x :=
  burgersFromHeat_burgers (initialHeatProfile_contDiff hu ν x₀).continuous
    (initialHeatProfile_bounded hν hU) (initialHeatProfile_pos ν u₀ x₀) hν t x ht

/-- The complete initial-value statement: joint positive-time `C²` regularity,
the Burgers equation, and recovery of the prescribed velocity as a right-hand trace. -/
theorem burgersSolution_solves_initial_value {u₀ : ℝ → ℝ} (hu : Continuous u₀)
    (hb : ∃ M, ∀ x, |u₀ x| ≤ M) {ν x₀ : ℝ} (hν : 0 < ν)
    (hU : ∃ L, ∀ x, L ≤ ∫ y in x₀..x, u₀ y) :
    ContDiffOn ℝ 2 (Function.uncurry (burgersSolution ν u₀ x₀)) (Ioi 0 ×ˢ univ) ∧
    (∀ t, 0 < t → ∀ x,
      deriv (fun s => burgersSolution ν u₀ x₀ s x) t +
        burgersSolution ν u₀ x₀ t x * deriv (burgersSolution ν u₀ x₀ t) x =
          ν * iteratedDeriv 2 (burgersSolution ν u₀ x₀ t) x) ∧
    (∀ x, Tendsto (fun t => burgersSolution ν u₀ x₀ t x) (𝓝[>] 0) (𝓝 (u₀ x))) :=
  ⟨burgersSolution_contDiffOn hu hν hU,
    fun t ht x => burgersSolution_burgers hu hν hU t x ht,
    burgersSolution_tendsto_zero hu hb hν hU⟩

end ColeHopf
