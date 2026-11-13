/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.CompensatorUniqueness
public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal
open MathlibExt.Probability.Statistics.CountingProcess.ContinuousTime

namespace MathlibExtTest.Probability.Statistics.CompensatorUniqueness

/-! ### Stopping and the hazard measure on explicit inputs -/

/-- With `Λ = δ₀`, `T = 2`, `C = 3`: the compensator after exit equals its value at exit `X = 2`
(computed from `compensator_eq`, not from the stopping lemma). -/
example (ω : ℝ) :
    compensator (fun _ : ℝ => (2 : ℝ)) (fun _ => 3) (Measure.dirac 0) 5 ω = 1 ∧
      compensator (fun _ : ℝ => (2 : ℝ)) (fun _ => 3) (Measure.dirac 0)
        (min 5 (obsTime (fun _ : ℝ => (2 : ℝ)) (fun _ => 3) ω)) ω = 1 := by
  simp [compensator_eq, obsTime]

/-- Before the hazard's atom the compensator is `0`. -/
example (ω : ℝ) :
    compensator (fun _ : ℝ => (2 : ℝ)) (fun _ => 3) (Measure.dirac 0) (-1) ω = 0 := by
  simp [compensator_eq, obsTime]

example (ω : ℝ) :
    compensator (fun _ : ℝ => (2 : ℝ)) (fun _ => 3) (Measure.dirac 0) 5 ω =
      compensator (fun _ : ℝ => (2 : ℝ)) (fun _ => 3) (Measure.dirac 0)
        (min 5 (obsTime (fun _ : ℝ => (2 : ℝ)) (fun _ => 3) ω)) ω :=
  compensator_min_obsTime _ 5 ω

/-! ### A nondegenerate model: standard Gaussian failure time, censoring at `1` -/

/-- The standard Gaussian law charges every right half-line (it dominates Lebesgue measure). -/
theorem gaussianReal_Ici_ne_zero (s : ℝ) : gaussianReal 0 1 (Ici s) ≠ 0 := fun h => by
  have := gaussianReal_absolutelyContinuous' 0 one_ne_zero h
  simp [Real.volume_Ici] at this

/-- Hence its hazard measure is finite on every left half-line. -/
theorem hazard_gaussian_Iic_ne_top (s : ℝ) :
    hazardMeasure ((gaussianReal 0 1).map id) (Iic s) ≠ ∞ := by
  rw [Measure.map_id]
  exact hazardMeasure_Iic_ne_top (gaussianReal_Ici_ne_zero s)

/-- The counting process of this model is genuinely random: at `t = 2` it is `1` at `ω = 0`
(failure at `0`, observed) and `0` at `ω = 3` (censored at `1`). -/
example : countingProcess id (fun _ : ℝ => (1 : ℝ)) 2 0 = 1 ∧
    countingProcess id (fun _ : ℝ => (1 : ℝ)) 2 3 = 0 := by
  norm_num [countingProcess]

/-- **Non-vacuity.** Every hypothesis of `ae_forall_eq_of_isCompensator_history` holds for the
model compensator in the Gaussian model, so the uniqueness theorem applies to it. -/
example : ∀ᵐ ω ∂(gaussianReal 0 1), ∀ t,
    compensator id (fun _ : ℝ => (1 : ℝ)) (hazardMeasure ((gaussianReal 0 1).map id)) t ω =
      compensator id (fun _ : ℝ => (1 : ℝ)) (hazardMeasure ((gaussianReal 0 1).map id)) t ω := by
  have hind : IndepFun id (fun _ : ℝ => (1 : ℝ)) (gaussianReal 0 1) := indepFun_const_right _ _
  have hfv := fun ω => ((monotone_compensator (T := id) (C := fun _ : ℝ => (1 : ℝ))
    hazard_gaussian_Iic_ne_top ω).monotoneOn univ).locallyBoundedVariationOn
  exact ae_forall_eq_of_isCompensator_history measurable_id measurable_const
    (martingale_compensatedProcess measurable_id measurable_const hind)
    (martingale_compensatedProcess measurable_id measurable_const hind)
    (measurable_compensator_strictPast measurable_id measurable_const _)
    (measurable_compensator_strictPast measurable_id measurable_const _)
    (compensator_min_obsTime _) (compensator_min_obsTime _) hfv hfv
    (tendsto_compensator_atBot hazard_gaussian_Iic_ne_top)
    (tendsto_compensator_atBot hazard_gaussian_Iic_ne_top)

/-- The model-level corollary, instantiated in the Gaussian model. -/
example : ∀ᵐ ω ∂(gaussianReal 0 1), ∀ t,
    compensator id (fun _ : ℝ => (1 : ℝ)) (hazardMeasure ((gaussianReal 0 1).map id)) t ω =
      compensator id (fun _ : ℝ => (1 : ℝ)) (hazardMeasure ((gaussianReal 0 1).map id)) t ω :=
  ae_forall_eq_compensator measurable_id measurable_const (indepFun_const_right _ _)
    hazard_gaussian_Iic_ne_top
    (martingale_compensatedProcess measurable_id measurable_const (indepFun_const_right _ _))
    (measurable_compensator_strictPast measurable_id measurable_const _)
    (compensator_min_obsTime _)
    (fun ω => ((monotone_compensator hazard_gaussian_Iic_ne_top ω).monotoneOn
      univ).locallyBoundedVariationOn)
    (tendsto_compensator_atBot hazard_gaussian_Iic_ne_top)

/-! ### Boundary: the normalization `A(-∞) = 0` cannot be dropped -/

/-- `A + 1` keeps the martingale, predictability and stopping properties of the model compensator
`A`, differs from `A` everywhere, and tends to `1` (not `0`) at `-∞`. So without the normalization
hypothesis compensators are only unique up to an additive constant. -/
example :
    Martingale (fun t => countingProcess id (fun _ : ℝ => (1 : ℝ)) t - fun ω =>
        compensator id (fun _ : ℝ => (1 : ℝ)) (hazardMeasure ((gaussianReal 0 1).map id)) t ω + 1)
      (historyFiltration (C := fun _ : ℝ => (1 : ℝ)) measurable_id measurable_const)
      (gaussianReal 0 1) ∧
    (∀ t ω,
      compensator id (fun _ : ℝ => (1 : ℝ)) (hazardMeasure ((gaussianReal 0 1).map id)) t ω + 1 ≠
        compensator id (fun _ : ℝ => (1 : ℝ)) (hazardMeasure ((gaussianReal 0 1).map id)) t ω) ∧
    (∀ ω, Tendsto (fun t =>
      compensator id (fun _ : ℝ => (1 : ℝ)) (hazardMeasure ((gaussianReal 0 1).map id)) t ω + 1)
        atBot (𝓝 1)) := by
  refine ⟨?_, fun t ω => by linarith, fun ω => by
    simpa using (tendsto_compensator_atBot hazard_gaussian_Iic_ne_top ω).add_const 1⟩
  have h := (martingale_compensatedProcess measurable_id measurable_const
    (indepFun_const_right id (1 : ℝ)) (μ := gaussianReal 0 1)).sub
    (martingale_const (historyFiltration measurable_id measurable_const) (gaussianReal 0 1) 1)
  convert h using 1
  funext t ω
  simp only [compensatedProcess, Pi.sub_apply]
  ring

end MathlibExtTest.Probability.Statistics.CompensatorUniqueness
