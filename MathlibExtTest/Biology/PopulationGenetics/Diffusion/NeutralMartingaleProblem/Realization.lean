/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralMartingaleProblem.Realization

/-!
# Tests for the neutral Wright--Fisher realization with its natural filtration

Each public declaration is exercised on the constructed process (no process is
supplied by the caller), at an interior initial frequency and at both
absorbing boundary states.
-/

namespace MathlibExtTest.Biology.PopulationGenetics.Diffusion.NeutralMartingaleProblem.Realization

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ProbabilityTheory unitInterval

open MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralWrightFisherRaw
open MathlibExt.Biology.PopulationGenetics.Diffusion.WrightFisherSemigroup
open MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralMartingaleProblem

/-- The interior initial frequency `1/2`. -/
noncomputable def xHalf : I := ⟨1 / 2, by constructor <;> norm_num⟩

/-! Kernel facts. -/

example (t : ℝ≥0) : ∫ y, (y : ℝ) ∂neutralKernel t xHalf = 1 / 2 :=
  integral_neutralKernel_coe t xHalf

example : neutralKernel 3 0 = Measure.dirac 0 := neutralKernel_apply_zero_state 3

example : neutralKernel 3 1 = Measure.dirac 1 := neutralKernel_apply_one_state 3

/-! State-valued view of the realization. -/

example (t : ℝ≥0) (ω : SamplePath) :
    (modifiedState xHalf t ω : ℝ) = modifiedProcess xHalf t ω :=
  coe_modifiedState xHalf t ω

example (t : ℝ≥0) : Measurable (modifiedState xHalf t) := measurable_modifiedState xHalf t

example (ω : SamplePath) : Continuous fun t => modifiedState xHalf t ω :=
  continuous_modifiedState xHalf ω

example (ω : SamplePath) : modifiedState xHalf 0 ω = xHalf := modifiedState_zero xHalf ω

example : modifiedState xHalf 2 =ᵐ[rawMeasure xHalf] fun ω => ω 2 :=
  modifiedState_ae_eq_eval xHalf 2

/-! Laws of the realization. -/

example : (rawMeasure xHalf).map (modifiedState xHalf 1) = neutralKernel 1 xHalf :=
  map_modifiedState xHalf 1

/-- At time zero the one-time law is the point mass at the initial state. -/
example : (rawMeasure xHalf).map (modifiedState xHalf 0) = Measure.dirac xHalf := by
  rw [map_modifiedState, neutralKernel_zero, Kernel.id_apply]

example :
    (rawMeasure xHalf).map (modifiedProcess xHalf 1) =
      (neutralKernel 1 xHalf).map ((↑) : I → ℝ) :=
  map_modifiedProcess xHalf 1

example :
    (rawMeasure xHalf).map (fun ω => (modifiedState xHalf 1 ω, modifiedState xHalf 3 ω)) =
      (neutralKernel 1 xHalf) ⊗ₘ neutralKernel 2 := by
  have h := map_modifiedState_pair_of_lt xHalf (s := 1) (t := 3) (by norm_num)
  have h2 : (3 : ℝ≥0) - 1 = 2 := by
    rw [tsub_eq_iff_eq_add_of_le (by norm_num)]
    norm_num
  rwa [h2] at h

/-- Semigroup identity on the constant test function `1`. -/
example (t : ℝ≥0) : ∫ ω, (1 : C(I, ℝ)) (modifiedState xHalf t ω) ∂rawMeasure xHalf = 1 := by
  rw [integral_modifiedState, wfSemigroup_apply_one]
  rfl

/-- Semigroup identity on the non-constant coordinate test function: the
semigroup applied to `y ↦ y` at `1/2` is the mean of the realization, `1/2`. -/
example (t : ℝ≥0) :
    wfSemigroup t ⟨fun y : I => (y : ℝ), by fun_prop⟩ xHalf = 1 / 2 := by
  rw [← integral_modifiedState]
  exact integral_modifiedProcess xHalf t

/-- The mean of the realization started at `1/2` stays `1/2`. -/
example (t : ℝ≥0) : ∫ ω, modifiedProcess xHalf t ω ∂rawMeasure xHalf = 1 / 2 :=
  integral_modifiedProcess xHalf t

/-! The natural filtration. -/

example : StronglyAdapted (naturalFiltration xHalf) (modifiedProcess xHalf) :=
  stronglyAdapted_naturalFiltration xHalf

example : Measurable[naturalFiltration xHalf 5] (modifiedProcess xHalf 2) :=
  measurable_modifiedProcess_naturalFiltration xHalf (by norm_num)

/-- The filtration at each time is a sub-σ-algebra of the path σ-algebra. -/
example (t : ℝ≥0) : naturalFiltration xHalf t ≤ (inferInstance : MeasurableSpace SamplePath) :=
  (naturalFiltration xHalf).le t

/-! Absorbing boundary states. -/

example : ∀ᵐ ω ∂rawMeasure 0, ∀ t, modifiedProcess 0 t ω = 0 :=
  ae_forall_modifiedProcess_zero

example : ∀ᵐ ω ∂rawMeasure 1, ∀ t, modifiedProcess 1 t ω = 1 :=
  ae_forall_modifiedProcess_one

/-- Boundary consistency: the absorbing statement agrees with the mean formula. -/
example (t : ℝ≥0) : ∫ ω, modifiedProcess 1 t ω ∂rawMeasure 1 = 1 := by
  rw [integral_modifiedProcess]
  rfl

#print axioms integral_neutralKernel_coe
#print axioms neutralKernel_apply_zero_state
#print axioms neutralKernel_apply_one_state
#print axioms map_modifiedState
#print axioms map_modifiedState_pair_of_lt
#print axioms integral_modifiedState
#print axioms integral_modifiedProcess
#print axioms stronglyAdapted_naturalFiltration
#print axioms measurable_modifiedProcess_naturalFiltration
#print axioms ae_forall_modifiedProcess_zero
#print axioms ae_forall_modifiedProcess_one

end MathlibExtTest.Biology.PopulationGenetics.Diffusion.NeutralMartingaleProblem.Realization
