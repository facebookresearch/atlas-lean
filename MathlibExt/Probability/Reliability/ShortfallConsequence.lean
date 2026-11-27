/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Statistics.ModelInterop
public import MathlibExt.Probability.Reliability.LimitState

/-!
# Shortfall consequence and extended risk

For a resistance `R` and load effect `S` on one probability
space (no independence assumed), the shortfall consequence is
the positive part of `S - R` as a nonnegative loss. It vanishes
off the limit-state failure event, is measurable for measurable
`R` and `S`, and its extended risk (deterministic-kernel bind
form and extended frequentist risk alike) is the extended
expected shortfall, which accumulates only on the failure
event. No integrability is assumed; the value may be infinite.

## Main results

- `Reliability.shortfallConsequence_eq_zero_iff`: the
  shortfall vanishes exactly when the load does not exceed the
  resistance.
- `Reliability.shortfallConsequence_measurable`:
  measurability from measurable inputs.
- `Reliability.shortfallConsequence_bind_eq`: the extended-risk
  bridge and the failure-event form.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Reliability

/-- Shortfall consequence of a limit-state pair: the positive
part of load effect minus resistance, as a nonnegative finite
loss at each outcome. It vanishes outside the failure event
(R - S ≤ 0) and equals the shortfall (S - R) inside it. No
bound or integrability is imposed. -/
noncomputable def shortfallConsequence {Ω : Type*}
    (R S : Ω → ℝ) (ω : Ω) : NNReal :=
  Real.toNNReal (S ω - R ω)

/-- The shortfall consequence is zero exactly when the load does
not exceed the resistance; on the failure event it is zero only
at equality. -/
theorem shortfallConsequence_eq_zero_iff {Ω : Type*}
    {R S : Ω → ℝ} {ω : Ω} :
    shortfallConsequence R S ω = 0 ↔ S ω ≤ R ω := by
  simp only [shortfallConsequence, Real.toNNReal_eq_zero, sub_nonpos]

/-- The shortfall consequence vanishes off the failure event. -/
theorem shortfallConsequence_eq_zero_of_notMem {Ω : Type*}
    {R S : Ω → ℝ} {ω : Ω} (hω : ω ∉ failureEvent R S) :
    shortfallConsequence R S ω = 0 := by
  rw [shortfallConsequence_eq_zero_iff]
  rw [mem_failureEvent] at hω
  exact (not_le.mp hω).le

/-- The shortfall consequence is measurable for measurable
resistance and load variables. -/
theorem shortfallConsequence_measurable {Ω : Type*}
    [MeasurableSpace Ω] {R S : Ω → ℝ} (hR : Measurable R)
    (hS : Measurable S) :
    Measurable (shortfallConsequence R S) := by
  unfold shortfallConsequence
  exact (hS.sub hR).real_toNNReal

/-- Extended-risk bridge for the shortfall consequence. On one
joint probability law for the resistance and load variables,
with no independence or integrability assumption, pushing the
law through the deterministic shortfall response gives the same
extended value as the extended frequentist risk of that
response with identity loss, and both equal the extended
expected shortfall, which accumulates only on the failure
event. All values are in the extended nonnegative reals and
may be infinite. -/
theorem shortfallConsequence_bind_eq {Ω : Type*}
    [MeasurableSpace Ω] {R S : Ω → ℝ} (μ : ProbabilityMeasure Ω)
    (hC : Measurable (shortfallConsequence R S)) :
    ∫⁻ a, ((a : NNReal) : ℝ≥0∞)
        ∂((μ : Measure Ω).bind
          (Kernel.deterministic (shortfallConsequence R S) hC))
      = MathlibExt.Probability.Statistics.EstimationRisk.frequentistRiskENN
          (shortfallConsequence R S) (fun _ : Unit => μ)
          (fun _ a => a) ()
    ∧ ∫⁻ a, ((a : NNReal) : ℝ≥0∞)
        ∂((μ : Measure Ω).bind
          (Kernel.deterministic (shortfallConsequence R S) hC))
      = ∫⁻ ω, ENNReal.ofReal (S ω - R ω) ∂(μ : Measure Ω)
    ∧ ∫⁻ ω, ENNReal.ofReal (S ω - R ω) ∂(μ : Measure Ω)
      = ∫⁻ ω in failureEvent R S, ENNReal.ofReal (S ω - R ω)
          ∂(μ : Measure Ω) := by
  have hbridge :=
    MathlibExt.Probability.Statistics.EstimationRisk.lintegral_deterministic_bind_eq_frequentistRiskENN
      (shortfallConsequence R S) hC (fun _ : Unit => μ) (fun _ a => a) ()
      measurable_coe_nnreal_ennreal
  refine ⟨hbridge, hbridge.trans ?_, ?_⟩
  · show ∫⁻ x, ((shortfallConsequence R S x : NNReal) : ℝ≥0∞) ∂(μ : Measure Ω)
        = ∫⁻ ω, ENNReal.ofReal (S ω - R ω) ∂(μ : Measure Ω)
    refine lintegral_congr fun ω ↦ ?_
    unfold shortfallConsequence
    exact ENNReal.ofNNReal_toNNReal _
  · have hsup : (fun ω => ENNReal.ofReal (S ω - R ω)).support
        ⊆ failureEvent R S := by
      intro ω hω
      rw [Function.mem_support] at hω
      rw [mem_failureEvent]
      by_contra hle
      exact hω (ENNReal.ofReal_eq_zero.mpr (sub_nonpos.mpr (not_le.mp hle).le))
    exact (setLIntegral_eq_of_support_subset hsup).symm

end Reliability
