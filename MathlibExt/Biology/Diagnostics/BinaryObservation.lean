/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.Real

/-!
# Binary diagnostic observation: PPV coverage transfer

For a binary diagnostic with parameters `θ = (π, se, sp)` (prevalence,
sensitivity, specificity) as in
`MathlibExt.Probability.Statistics.DiagnosticObservation.JointLaw`, any
joint confidence set for `θ`, not necessarily rectangular, transfers
conservative coverage to a PPV output set containing the PPV image:
the PPV coverage event has at least the measure of the joint coverage
event. Only the PPV denominator appears; a zero NPV denominator does
not invalidate the PPV statement (the singleton `(1, 1, 1)` has PPV
`1` with zero negative-test mass).

Model mathematics only; no screening or clinical claim.
-/

@[expose] public section

open MeasureTheory Set

namespace MathlibExt.Biology.Diagnostics.BinaryObservation

set_option linter.unusedVariables false in
/-- **PPV coverage transfer.** Let `θ ω = (π, se, sp)` be the true
diagnostic parameters, `S ω` a joint confidence set for them with
measurable coverage event, and `T ω` a PPV output set with measurable
coverage event. If `T ω` contains the PPV image value
`π * se / (π * se + (1 - π) * (1 - sp))` whenever `θ ω ∈ S ω`, then
the PPV coverage event has at least the measure of the joint coverage
event: coverage transfers conservatively through the PPV map, for any
(not necessarily rectangular) joint set. Only the PPV denominator
appears; no NPV denominator condition is imposed. -/
theorem ppv_coverage_transfer {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Ω → Set (ℝ × ℝ × ℝ)) (θ : Ω → ℝ × ℝ × ℝ) (T : Ω → Set ℝ)
    (hS : MeasurableSet {ω | θ ω ∈ S ω})
    (hT : MeasurableSet {ω | (θ ω).1 * (θ ω).2.1 /
      ((θ ω).1 * (θ ω).2.1 + (1 - (θ ω).1) * (1 - (θ ω).2.2)) ∈ T ω})
    (hcov : ∀ ω, θ ω ∈ S ω →
      (θ ω).1 * (θ ω).2.1 /
        ((θ ω).1 * (θ ω).2.1 + (1 - (θ ω).1) * (1 - (θ ω).2.2)) ∈ T ω) :
    μ.real {ω | θ ω ∈ S ω} ≤
      μ.real {ω | (θ ω).1 * (θ ω).2.1 /
        ((θ ω).1 * (θ ω).2.1 + (1 - (θ ω).1) * (1 - (θ ω).2.2)) ∈ T ω} := by
  exact measureReal_mono (fun ω hω => hcov ω hω) (measure_ne_top _ _)

/-- The singleton parameter `(π, se, sp) = (1, 1, 1)` has PPV `1`
although its negative-test mass `(1 - π) * sp + π * (1 - se)` is zero:
a zero NPV denominator does not invalidate the PPV value. -/
theorem ppv_one_one_one :
    (1 : ℝ) * 1 / ((1 : ℝ) * 1 + (1 - 1) * (1 - 1)) = 1 := by
  norm_num

end MathlibExt.Biology.Diagnostics.BinaryObservation
