/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.ContinuousMapping
public import Mathlib.MeasureTheory.Measure.Dirac.Def
public import Mathlib.MeasureTheory.Measure.Dirac.Basic

@[expose] public section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped BoundedContinuousFunction

namespace MathlibExtTest.Probability.ContinuousMapping

/-- A function that is discontinuous at `0` (it jumps from `x` to `1`) and
continuous everywhere else. It is measurable and continuous almost everywhere
with respect to any measure that gives no mass to `{0}`. -/
noncomputable def spikeZero : ℝ → ℝ := fun y ↦ if y = 0 then 1 else y

/-- `spikeZero` is measurable: it is `1` on the measurable singleton `{0}`
and the identity elsewhere. -/
theorem spikeZero_measurable : Measurable spikeZero :=
  Measurable.ite (measurableSet_singleton (0 : ℝ)) measurable_const measurable_id

/-- `spikeZero` is continuous at every `x ≠ 0`: near such an `x` it agrees
with the identity function. -/
theorem spikeZero_continuousAt_of_ne {x : ℝ} (hx : x ≠ 0) :
    ContinuousAt spikeZero x := by
  apply ContinuousAt.congr continuousAt_id
  filter_upwards [isOpen_compl_singleton.mem_nhds hx] with y hy
  have hy0 : ¬ y = 0 := by simpa using hy
  simp [spikeZero, hy0]

/-- The discontinuity set of `spikeZero` is contained in `{0}`. -/
theorem spikeZero_discontinuity_subset : {x : ℝ | ¬ContinuousAt spikeZero x} ⊆ {0} := by
  intro x hx
  by_contra hx0
  have hxne : x ≠ 0 := by simpa using hx0
  exact hx (spikeZero_continuousAt_of_ne hxne)

/-- The Dirac measure at `1` gives no mass to the discontinuity set of
`spikeZero`, since that set is contained in `{0}` and `1 ∉ {0}`. -/
theorem spikeZero_discontinuity_dirac_one_null :
    (Measure.dirac (1 : ℝ)) {x : ℝ | ¬ContinuousAt spikeZero x} = 0 := by
  refine le_antisymm ?_ zero_le
  calc (Measure.dirac (1 : ℝ)) {x : ℝ | ¬ContinuousAt spikeZero x}
      ≤ (Measure.dirac (1 : ℝ)) {0} := measure_mono spikeZero_discontinuity_subset
    _ = 0 := by simp

/-- The integral form of the continuous mapping theorem restates with the
exact public signature. -/
example (μs : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (μs n)]
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (g : ℝ → ℝ) (hg_meas : Measurable g)
    (hg_ae : μ {x | ¬ContinuousAt g x} = 0)
    (hconv : ∀ f : ℝ →ᵇ ℝ,
      Tendsto (fun n ↦ ∫ x, f x ∂(μs n)) atTop (𝓝 (∫ x, f x ∂μ))) :
    ∀ f : ℝ →ᵇ ℝ,
      Tendsto (fun n ↦ ∫ x, f x ∂((μs n).map g)) atTop
        (𝓝 (∫ x, f x ∂(μ.map g))) :=
  continuous_mapping μs μ g hg_meas hg_ae hconv

/-- The probability-measure form restates with the exact public signature. -/
example {μs : ℕ → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    {g : ℝ → ℝ} (hg_meas : Measurable g)
    (hg_ae : (μ : Measure ℝ) {x | ¬ContinuousAt g x} = 0)
    (hconv : Tendsto μs atTop (𝓝 μ)) :
    Tendsto (fun n ↦ (μs n).map g) atTop (𝓝 (μ.map g)) :=
  ProbabilityMeasure.tendsto_map_of_tendsto_of_ae_continuous hg_meas hg_ae hconv

/-- Genuine a.e.-continuous example: pushforward of the constant sequence at
the Dirac measure at `1` by `spikeZero`, which is discontinuous at `0`.
The Dirac measure at `1` charges the discontinuity set with mass `0`, so
the continuous mapping theorem applies even though `spikeZero` is not
continuous. -/
example :
    Tendsto (fun _n : ℕ ↦
      ProbabilityMeasure.map (Measure.dirac (1 : ℝ)).toProbabilityMeasure spikeZero)
      atTop
      (𝓝 (ProbabilityMeasure.map (Measure.dirac (1 : ℝ)).toProbabilityMeasure spikeZero)) := by
  apply ProbabilityMeasure.tendsto_map_of_tendsto_of_ae_continuous
    (μs := fun _ ↦ (Measure.dirac (1 : ℝ)).toProbabilityMeasure)
    (μ := (Measure.dirac (1 : ℝ)).toProbabilityMeasure)
    spikeZero_measurable
  · exact spikeZero_discontinuity_dirac_one_null
  · exact tendsto_const_nhds

/-- The same example in integral form, for the constant test function `1`:
pushforwards of a constant sequence converge to the pushforward of the
limit, for a discontinuous-but-a.e.-continuous map. -/
example :
    Tendsto (fun _n : ℕ ↦
      ∫ x, (1 : ℝ →ᵇ ℝ) x ∂((Measure.dirac (1 : ℝ)).map spikeZero))
      atTop
      (𝓝 (∫ x, (1 : ℝ →ᵇ ℝ) x ∂((Measure.dirac (1 : ℝ)).map spikeZero))) := by
  apply continuous_mapping (μs := fun _ ↦ Measure.dirac (1 : ℝ))
    (μ := Measure.dirac (1 : ℝ)) (g := spikeZero) spikeZero_measurable
    spikeZero_discontinuity_dirac_one_null
  intro f
  exact tendsto_const_nhds

/-- Continuous maps are also covered: pushforward by `x ↦ x + 1` of a
constant sequence converges. -/
example :
    Tendsto (fun _n : ℕ ↦
      ProbabilityMeasure.map (Measure.dirac (1 : ℝ)).toProbabilityMeasure
        (fun x : ℝ ↦ x + 1))
      atTop
      (𝓝 (ProbabilityMeasure.map (Measure.dirac (1 : ℝ)).toProbabilityMeasure
        (fun x : ℝ ↦ x + 1))) := by
  apply ProbabilityMeasure.tendsto_map_of_tendsto_of_ae_continuous
    (μs := fun _ ↦ (Measure.dirac (1 : ℝ)).toProbabilityMeasure)
    (μ := (Measure.dirac (1 : ℝ)).toProbabilityMeasure)
    (by fun_prop)
  · have h : {x : ℝ | ¬ContinuousAt (fun y : ℝ ↦ y + 1) x} = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun x hx ↦
        hx ((continuous_id.add continuous_const).continuousAt)
    rw [h]
    simp
  · exact tendsto_const_nhds

-- `#print axioms` for the public declarations: only the standard triple.
#print axioms ProbabilityTheory.continuous_mapping
#print axioms MeasureTheory.ProbabilityMeasure.tendsto_map_of_tendsto_of_ae_continuous

end MathlibExtTest.Probability.ContinuousMapping
