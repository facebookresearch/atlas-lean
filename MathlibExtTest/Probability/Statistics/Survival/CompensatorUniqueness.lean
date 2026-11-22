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

/-- The model compensator `A(t) = Λ((-∞, t ∧ X])` of the Gaussian model. -/
local notation "Ag" =>
  compensator id (fun _ : ℝ => (1 : ℝ)) (hazardMeasure (Measure.map id (gaussianReal 0 1)))

/-- The history filtration of the Gaussian model. -/
local notation "ℱg" =>
  historyFiltration (T := id) (C := fun _ : ℝ => (1 : ℝ)) measurable_id measurable_const

/-- Every path of the model compensator has finite variation (it is monotone). -/
theorem fv_Ag (ω : ℝ) : LocallyBoundedVariationOn (fun t => Ag t ω) univ :=
  ((monotone_compensator (hazard_gaussian_Iic_ne_top _)).monotoneOn univ).locallyBoundedVariationOn

/-- **Non-vacuity.** Every hypothesis of `ae_forall_eq_of_isCompensator_history` holds for the
model compensator in the Gaussian model, so the uniqueness theorem applies to it. -/
example : ∀ᵐ ω ∂(gaussianReal 0 1), ∀ t, Ag t ω = Ag t ω := by
  have hind : IndepFun id (fun _ : ℝ => (1 : ℝ)) (gaussianReal 0 1) := indepFun_const_right _ _
  exact ae_forall_eq_of_isCompensator_history measurable_id measurable_const
    (martingale_compensatedProcess measurable_id measurable_const hind)
    (martingale_compensatedProcess measurable_id measurable_const hind)
    (measurable_compensator_strictPast measurable_id measurable_const _)
    (measurable_compensator_strictPast measurable_id measurable_const _)
    (compensator_min_obsTime _) (compensator_min_obsTime _) (ae_of_all _ fv_Ag)
    (ae_of_all _ fv_Ag)
    (ae_of_all _ fun _ => tendsto_compensator_atBot (hazard_gaussian_Iic_ne_top _))
    (ae_of_all _ fun _ => tendsto_compensator_atBot (hazard_gaussian_Iic_ne_top _))

/-- The hazard measure of the standard Gaussian charges `(-∞, 0]`: there `dΛ ≥ dF`. -/
theorem hazard_gaussian_Iic_zero_ne_zero :
    hazardMeasure ((gaussianReal 0 1).map id) (Iic 0) ≠ 0 := by
  rw [Measure.map_id, hazardMeasure, withDensity_apply _ measurableSet_Iic]
  intro h
  have h1 : ∫⁻ _ in Iic (0 : ℝ), (1 : ℝ≥0∞) ∂gaussianReal 0 1 ≤
      ∫⁻ s in Iic 0, (gaussianReal 0 1 (Ici s))⁻¹ ∂gaussianReal 0 1 :=
    setLIntegral_mono' measurableSet_Iic fun _ _ => ENNReal.one_le_inv.2 prob_le_one
  rw [h, setLIntegral_const, one_mul, nonpos_iff_eq_zero] at h1
  have := gaussianReal_absolutelyContinuous' 0 one_ne_zero h1
  simp [Real.volume_Iic] at this

/-- On `{ω ≥ 0}` (exit time `X = ω ∧ 1 ≥ 0`) the model compensator is positive at `t = 0`,
computed from `compensator_eq`. -/
theorem Ag_zero_pos {ω : ℝ} (hω : 0 ≤ ω) : 0 < Ag 0 ω := by
  rw [compensator_eq, min_eq_left (show (0 : ℝ) ≤ obsTime id (fun _ : ℝ => (1 : ℝ)) ω from
    le_min hω zero_le_one)]
  exact ENNReal.toReal_pos hazard_gaussian_Iic_zero_ne_zero (hazard_gaussian_Iic_ne_top 0)

/-- **The theorem has content.** `N - 2A` is not a martingale: otherwise `2A` would be a second
predictable, stopped, finite-variation, normalized compensator, so `2A = A` almost surely by
`ae_forall_eq_compensator`, contradicting `A(0) > 0` on `{ω ≥ 0}`, which has positive mass. -/
example : ¬ Martingale (fun t => countingProcess id (fun _ : ℝ => (1 : ℝ)) t - fun ω => 2 * Ag t ω)
    ℱg (gaussianReal 0 1) := by
  intro hM
  have h := ae_forall_eq_compensator measurable_id measurable_const
    (indepFun_const_right id (1 : ℝ)) hM
    (fun t => (measurable_compensator_strictPast measurable_id measurable_const _ t).const_mul 2)
    (fun t ω => by rw [← compensator_min_obsTime])
    (ae_of_all _ fun _ => (((monotone_compensator (hazard_gaussian_Iic_ne_top _)).const_mul
      (by norm_num : (0 : ℝ) ≤ 2)).monotoneOn univ).locallyBoundedVariationOn)
    (ae_of_all _ fun _ => by
      simpa using (tendsto_compensator_atBot (hazard_gaussian_Iic_ne_top _)).const_mul 2)
  have hsub : Ici (0 : ℝ) ⊆ {ω | ¬ ∀ t, 2 * Ag t ω = Ag t ω} := fun ω (hω : 0 ≤ ω) h' => by
    have h0 := h' 0
    have := Ag_zero_pos hω
    linarith
  have hnull : gaussianReal 0 1 (Ici 0) = 0 := measure_mono_null hsub (ae_iff.1 h)
  exact gaussianReal_Ici_ne_zero 0 hnull

/-- The model-level corollary, instantiated in the Gaussian model. -/
example : ∀ᵐ ω ∂(gaussianReal 0 1), ∀ t, Ag t ω = Ag t ω :=
  ae_forall_eq_compensator measurable_id measurable_const (indepFun_const_right _ _)
    (martingale_compensatedProcess measurable_id measurable_const (indepFun_const_right _ _))
    (measurable_compensator_strictPast measurable_id measurable_const _)
    (compensator_min_obsTime _) (ae_of_all _ fv_Ag)
    (ae_of_all _ fun _ => tendsto_compensator_atBot (hazard_gaussian_Iic_ne_top _))

/-! ### Boundary: the normalization `A(-∞) = 0` cannot be dropped -/

/-- `A + 1` satisfies every hypothesis except the normalization: `N - (A + 1)` is a martingale,
`A + 1` is predictable, stopped at exit and of finite variation, but it tends to `1` (not `0`) at
`-∞`, and it differs from `A` everywhere. So without the normalization compensators are only
unique up to an additive constant. -/
example :
    Martingale (fun t => countingProcess id (fun _ : ℝ => (1 : ℝ)) t - fun ω => Ag t ω + 1)
      ℱg (gaussianReal 0 1) ∧
    (∀ t, Measurable[⨆ s < t, ℱg s] fun ω => Ag t ω + 1) ∧
    (∀ t ω, Ag t ω + 1 = Ag (min t (obsTime id (fun _ : ℝ => (1 : ℝ)) ω)) ω + 1) ∧
    (∀ ω, LocallyBoundedVariationOn (fun t => Ag t ω + 1) univ) ∧
    (∀ ω, Tendsto (fun t => Ag t ω + 1) atBot (𝓝 1)) ∧
    (∀ t ω, Ag t ω + 1 ≠ Ag t ω) := by
  refine ⟨?_, fun t => (measurable_compensator_strictPast measurable_id measurable_const _
      t).add_const 1, fun t ω => by rw [← compensator_min_obsTime], fun ω =>
      (((monotone_compensator (hazard_gaussian_Iic_ne_top _)).add_const 1).monotoneOn
        univ).locallyBoundedVariationOn, fun ω => by
    simpa using (tendsto_compensator_atBot (hazard_gaussian_Iic_ne_top _)).add_const 1,
    fun t ω => by linarith⟩
  have h := (martingale_compensatedProcess measurable_id measurable_const
    (indepFun_const_right id (1 : ℝ)) (μ := gaussianReal 0 1)).sub
    (martingale_const ℱg (gaussianReal 0 1) 1)
  convert h using 1
  funext t ω
  simp only [compensatedProcess, Pi.sub_apply]
  ring

end MathlibExtTest.Probability.Statistics.CompensatorUniqueness
