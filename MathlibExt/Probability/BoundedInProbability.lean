/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.MeasureTheory.Measure.TightNormed
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

/-!
# Convergence in distribution implies boundedness in probability

A sequence of random vectors `X n` in a finite-dimensional real inner product space that
converges in distribution is bounded in probability: for every `ε > 0` there is one radius `K`
with `P {K < ‖X n‖} ≤ ε` for every `n`.

## Main results

* `ProbabilityTheory.exists_forall_measure_lt_norm_le_of_tendstoInDistribution`.

The laws of `X n` form a tight set by `isTightMeasureSet_of_tendsto_charFun` (their
characteristic functions converge to that of the limit law), and
`tendsto_measure_norm_gt_of_isTightMeasureSet` turns tightness into the radius `K`.

## References

* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press (1998), Chapter 2
  (Prohorov's theorem: a sequence converging in distribution is uniformly tight).
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']

/-- A sequence of random vectors converging in distribution is bounded in probability: for every
`ε > 0` there is a radius `K` with `P {K < ‖X n‖} ≤ ε` for all `n`. -/
theorem exists_forall_measure_lt_norm_le_of_tendstoInDistribution {X : ℕ → Ω → E} {Z : Ω' → E}
    (h : TendstoInDistribution X atTop Z (fun _ ↦ P) P') {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ K : ℝ, ∀ n, P {ω | K < ‖X n ω‖} ≤ ε := by
  have hT : IsTightMeasureSet (Set.range fun n ↦ P.map (X n)) :=
    isTightMeasureSet_of_tendsto_charFun (f := charFun (P'.map Z))
      continuous_charFun.continuousAt fun t ↦ h.tendsto_charFun t
  obtain ⟨K, hK⟩ :=
    ((tendsto_measure_norm_gt_of_isTightMeasureSet hT).eventually (eventually_le_nhds hε)).exists
  refine ⟨K, fun n ↦ ?_⟩
  have hmeas : MeasurableSet {x : E | K < ‖x‖} := measurableSet_lt measurable_const measurable_norm
  calc P {ω | K < ‖X n ω‖} = P.map (X n) {x | K < ‖x‖} :=
        (Measure.map_apply_of_aemeasurable (h.forall_aemeasurable n) hmeas).symm
    _ ≤ ⨆ μ ∈ Set.range fun n ↦ P.map (X n), μ {x | K < ‖x‖} :=
        le_biSup (f := fun μ : Measure E ↦ μ {x | K < ‖x‖}) ⟨n, rfl⟩
    _ ≤ ε := hK

end ProbabilityTheory
