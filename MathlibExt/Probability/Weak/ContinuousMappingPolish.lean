/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.Topology.MetricSpace.Polish

/-!
# Continuous mapping on Polish and outer-approximation spaces

Weak convergence of probability measures is preserved by pushing forward along a measurable
map whose discontinuity set is null for the limiting measure.

The general theorem needs only an outer-approximation property on the source and an
opens-measurable target. The Polish corollary is the sequential Borel-space form.

## References

* F. Simenhaus, *Convergence of probability measures*, M2 lecture notes, Theorems 8 and 15.
* R. Durrett, *Probability: Theory and Examples*, Theorem 3.2.10.

An equivalent statement was previously formalized as
`StatMech.FK.tendsto_probabilityMeasure_map_of_ae_continuousAt` in the archived
`Atlas/StatisticalMechanics/Code/FK/PottsClusterSumContinuity.lean`, which is outside the
build; the proof here follows the same Portmanteau argument.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace MathlibExt.Probability

/-- **Continuous mapping theorem** (frozen pin). Weak convergence `μs → μ` implies weak
convergence of the pushforwards by any measurable `g` whose discontinuity set is `μ`-null. -/
theorem tendsto_map_of_tendsto_of_ae_continuousAt {Ω Ω' ι : Type*}
    [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]
    [MeasurableSpace Ω'] [TopologicalSpace Ω'] [OpensMeasurableSpace Ω']
    {L : Filter ι} [L.IsCountablyGenerated]
    {μs : ι → ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω} (hμ : Tendsto μs L (𝓝 μ))
    {g : Ω → Ω'} (hg : Measurable g) (hdisc : (μ : Measure Ω) {x | ¬ContinuousAt g x} = 0) :
    Tendsto (fun i => (μs i).map g) L (𝓝 (μ.map g)) := by
  apply tendsto_of_forall_isOpen_le_liminf'
  intro G hG
  have hae : g ⁻¹' G =ᵐ[(μ : Measure Ω)] interior (g ⁻¹' G) := by
    have hcont : ∀ᵐ x ∂(μ : Measure Ω), ContinuousAt g x := by
      rw [ae_iff]; exact hdisc
    refine EventuallyLE.antisymm ?_ interior_subset.eventuallyLE
    filter_upwards [hcont] with x hx hxin
    exact mem_interior_iff_mem_nhds.mpr (hx (hG.mem_nhds hxin))
  rw [ProbabilityMeasure.map_apply' _ hg.aemeasurable hG.measurableSet]
  calc (μ : Measure Ω) (g ⁻¹' G) = (μ : Measure Ω) (interior (g ⁻¹' G)) := measure_congr hae
    _ ≤ L.liminf fun i => (μs i : Measure Ω) (interior (g ⁻¹' G)) :=
        ProbabilityMeasure.le_liminf_measure_open_of_tendsto hμ isOpen_interior
    _ ≤ L.liminf fun i => (μs i : Measure Ω) (g ⁻¹' G) :=
        liminf_le_liminf (Eventually.of_forall fun i => measure_mono interior_subset)
    _ = L.liminf fun i => (((μs i).map g : ProbabilityMeasure Ω') : Measure Ω') G := by
        congr 1; funext i; rw [ProbabilityMeasure.map_apply' _ hg.aemeasurable hG.measurableSet]

/-- Record shape: `E` Polish with its Borel σ-algebra, sequential weak convergence. -/
theorem tendsto_map_of_tendsto_of_ae_continuousAt_polish {E F : Type*}
    [TopologicalSpace E] [PolishSpace E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace F] [MeasurableSpace F] [BorelSpace F]
    {μs : ℕ → ProbabilityMeasure E} {μ : ProbabilityMeasure E} (hμ : Tendsto μs atTop (𝓝 μ))
    {g : E → F} (hg : Measurable g) (hdisc : (μ : Measure E) {x | ¬ContinuousAt g x} = 0) :
    Tendsto (fun n => (μs n).map g) atTop (𝓝 (μ.map g)) := by
  let := TopologicalSpace.pseudoMetrizableSpacePseudoMetric E
  exact tendsto_map_of_tendsto_of_ae_continuousAt hμ hg hdisc

end MathlibExt.Probability
