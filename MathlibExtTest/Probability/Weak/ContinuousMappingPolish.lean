/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Weak.ContinuousMappingPolish
public import MathlibExt.Probability.ContinuousMapping
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Tests for continuous mapping on Polish spaces

The real-valued theorem is recovered as a special case, both from the general theorem
and from its Polish-space corollary. The examples then check the sup-norm functional on
`C([0,1], ℝ)` and a genuinely discontinuous indicator map.
-/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace MathlibExtTest.Probability.Weak.ContinuousMappingPolish

open MathlibExt.Probability

/-! The Atlas `ℝ`-only theorem is the special case `Ω = Ω' = ℝ`. -/
example {μs : ℕ → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ} {g : ℝ → ℝ}
    (hg : Measurable g) (hdisc : (μ : Measure ℝ) {x | ¬ContinuousAt g x} = 0)
    (hconv : Tendsto μs atTop (𝓝 μ)) :
    Tendsto (fun n => (μs n).map g) atTop (𝓝 (μ.map g)) :=
  tendsto_map_of_tendsto_of_ae_continuousAt hconv hg hdisc

/-! The Polish corollary, also at `Ω = Ω' = ℝ`. -/
example {μs : ℕ → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ} {g : ℝ → ℝ}
    (hg : Measurable g) (hdisc : (μ : Measure ℝ) {x | ¬ContinuousAt g x} = 0)
    (hconv : Tendsto μs atTop (𝓝 μ)) :
    Tendsto (fun n => (μs n).map g) atTop (𝓝 (μ.map g)) :=
  tendsto_map_of_tendsto_of_ae_continuousAt_polish hconv hg hdisc

/-! Acceptance test: the sup-norm functional on `C([0,1], ℝ)` (Borel σ-algebra). -/
section SupNorm
local instance : MeasurableSpace C(unitInterval, ℝ) := borel _
local instance : BorelSpace C(unitInterval, ℝ) := ⟨rfl⟩

example {μs : ℕ → ProbabilityMeasure C(unitInterval, ℝ)} {μ : ProbabilityMeasure C(unitInterval, ℝ)}
    (hμ : Tendsto μs atTop (𝓝 μ)) :
    Tendsto (fun n => (μs n).map (fun f : C(unitInterval, ℝ) => ‖f‖))
      atTop (𝓝 (μ.map (fun f : C(unitInterval, ℝ) => ‖f‖))) := by
  refine tendsto_map_of_tendsto_of_ae_continuousAt hμ
    (g := fun f : C(unitInterval, ℝ) => ‖f‖) continuous_norm.measurable ?_
  simp [continuous_norm.continuousAt]
end SupNorm

/-! A genuinely discontinuous map: the indicator of `[0, ∞)` is discontinuous only at `0`,
so any weak limit with no atom at `0` (e.g. `δ₁`) pushes forward. -/
example {μs : ℕ → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (hμ : Tendsto μs atTop (𝓝 μ)) (h0 : (μ : Measure ℝ) {0} = 0) :
    Tendsto (fun n => (μs n).map ((Ici (0 : ℝ)).indicator fun _ => (1 : ℝ)))
      atTop (𝓝 (μ.map ((Ici (0 : ℝ)).indicator fun _ => (1 : ℝ)))) := by
  refine tendsto_map_of_tendsto_of_ae_continuousAt hμ
    (measurable_const.indicator measurableSet_Ici) ?_
  have hsub : {x : ℝ | ¬ContinuousAt ((Ici (0 : ℝ)).indicator fun _ => (1 : ℝ)) x} ⊆ {0} := by
    intro x hx
    by_contra h0
    apply hx
    rcases lt_or_gt_of_ne (show x ≠ 0 from h0) with hneg | hpos
    · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
      filter_upwards [Iio_mem_nhds hneg] with y hy
      simp [Set.indicator, show ¬ (0 : ℝ) ≤ y from not_le.2 hy]
    · refine (continuousAt_const (y := (1 : ℝ))).congr ?_
      filter_upwards [Ioi_mem_nhds hpos] with y hy
      simp [Set.indicator, show (0 : ℝ) ≤ y from le_of_lt hy]
  exact measure_mono_null hsub h0

-- the hypothesis is satisfiable by a non-atomic-at-0 limit, e.g. `δ₁`
example : (Measure.dirac (1 : ℝ)) {0} = 0 := by simp

#print axioms MathlibExt.Probability.tendsto_map_of_tendsto_of_ae_continuousAt
#print axioms MathlibExt.Probability.tendsto_map_of_tendsto_of_ae_continuousAt_polish

end MathlibExtTest.Probability.Weak.ContinuousMappingPolish
