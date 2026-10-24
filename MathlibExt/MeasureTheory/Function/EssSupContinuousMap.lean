/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Function.EssSup
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Topology.ContinuousMap.Compact

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace MathlibExt.MeasureTheory.Function.EssSupContinuousMap

/-!
# Essential supremum of a continuous map

For a continuous map `f : C(α, E)` on a compact space `α` equipped with a Borel
measure `μ` that is positive on nonempty open sets, the essential supremum
`‖f‖_{L^∞(μ)}` coincides with the usual supremum norm `‖f‖ₑ`.

Source: `v1/Atlas/IntroductionToFunctionalAnalysis/code/LpSpaces.lean`,
`LpSpaces.eLpNormEssSup_eq_enorm_continuousMap` and the second part of
`LpSpaces.essSup_properties` (Proposition, Essential supremum properties,
April 6, 2021 section). The first part of `essSup_properties` is Mathlib's
`ae_le_eLpNormEssSup` and is not re-ported.
-/

/-- **Essential supremum of a continuous map.** Let `α` be compact, `μ` a Borel
measure on `α` positive on nonempty open sets, and `f : C(α, E)` continuous.
Then the essential supremum of `f` with respect to `μ` equals the supremum
norm `‖f‖ₑ` of `f`. In particular, on `[a, b]` with `f ∈ C([a, b])`,
`‖f‖_{L^∞([a, b])} = ‖f‖_∞`. -/
theorem eLpNormEssSup_eq_enorm_continuousMap
    {α : Type*} [TopologicalSpace α] [CompactSpace α] [MeasurableSpace α]
    [BorelSpace α] {μ : Measure α} [μ.IsOpenPosMeasure]
    {E : Type*} [SeminormedAddCommGroup E] (f : C(α, E)) :
    eLpNormEssSup (fun x => f x) μ = ‖f‖ₑ := by
  rw [eLpNormEssSup_eq_essSup_enorm]
  set g : α → ℝ≥0∞ := fun x => ‖f x‖ₑ with hg
  have hcont : Continuous g := continuous_enorm.comp f.continuous
  have h_essSup_eq : essSup g μ = ⨆ x, g x := by
    apply le_antisymm
    · exact essSup_le_of_ae_le _ (by filter_upwards with x; exact le_iSup g x)
    · apply iSup_le
      intro x
      by_contra h
      simp only [not_le] at h
      have hopen : IsOpen {y | essSup g μ < g y} := hcont.isOpen_preimage _ isOpen_Ioi
      have hpos := hopen.measure_pos μ ⟨x, h⟩
      have hzero : μ {y | essSup g μ < g y} = 0 :=
        measure_mono_null (fun y hy => not_le.mpr hy) (ae_iff.mp (ae_le_essSup (f := g)))
      exact absurd hzero (ne_of_gt hpos)
  rw [h_essSup_eq]
  exact (ContinuousMap.enorm_eq_iSup_enorm f).symm

/-- **The `L^∞` norm of a continuous map is its supremum norm.** Under the same
hypotheses, `‖f‖_{L^∞(μ)} = ‖f‖ₑ`. The `SecondCountableTopologyEither`
hypothesis is what current Mathlib requires for `Continuous.aestronglyMeasurable`;
it holds, for instance, whenever `α` is second-countable. -/
theorem eLpNorm_top_eq_enorm_continuousMap
    {α : Type*} [TopologicalSpace α] [CompactSpace α] [MeasurableSpace α]
    [BorelSpace α] {μ : Measure α} [μ.IsOpenPosMeasure]
    {E : Type*} [SeminormedAddCommGroup E] [SecondCountableTopologyEither α E]
    (f : C(α, E)) :
    eLpNorm (fun x => f x) ⊤ μ = ‖f‖ₑ := by
  rw [eLpNorm_exponent_top f.continuous.aestronglyMeasurable]
  exact eLpNormEssSup_eq_enorm_continuousMap f

#print axioms eLpNormEssSup_eq_enorm_continuousMap
#print axioms eLpNorm_top_eq_enorm_continuousMap

end MathlibExt.MeasureTheory.Function.EssSupContinuousMap
