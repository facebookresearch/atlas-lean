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

/-- The positive predictive value of parameters `θ = (π, se, sp)` as
a real ratio (a genuine predictive value on the admissible domain
where the denominator is positive). -/
noncomputable def ppv (θ : ℝ × ℝ × ℝ) : ℝ :=
  θ.1 * θ.2.1 / (θ.1 * θ.2.1 + (1 - θ.1) * (1 - θ.2.2))

/-- The PPV formula unfolded. -/
theorem ppv_eq (θ : ℝ × ℝ × ℝ) :
    ppv θ = θ.1 * θ.2.1 / (θ.1 * θ.2.1 + (1 - θ.1) * (1 - θ.2.2)) := rfl

set_option linter.unusedVariables false in
/-- **PPV coverage transfer.** Let `θ ω = (π, se, sp)` be the true
diagnostic parameters, `S ω` a joint confidence set for them, and
`T ω` a conservative PPV output set containing the transformed
covered value (`θ ω ∈ S ω → ppv (θ ω) ∈ T ω`). On the admissible
domain, whenever `θ ω ∈ S ω` the parameters lie in
`π, se, sp ∈ [0, 1]` and the PPV denominator is strictly positive.
Then the coverage event for `T` has at least the measure of the
joint coverage event: coverage transfers conservatively through the
PPV map, for any (not necessarily rectangular) joint set and any
measurable conservative output set. Only the PPV denominator
appears; no NPV denominator condition is imposed. -/
theorem ppv_coverage_transfer {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Ω → Set (ℝ × ℝ × ℝ)) (T : Ω → Set ℝ) (θ : Ω → ℝ × ℝ × ℝ)
    (hS : MeasurableSet {ω | θ ω ∈ S ω})
    (hT : MeasurableSet {ω | ppv (θ ω) ∈ T ω})
    (hcover : ∀ ω, Set.image ppv (S ω) ⊆ T ω)
    (hdom : ∀ ω, θ ω ∈ S ω →
      0 ≤ (θ ω).1 ∧ (θ ω).1 ≤ 1 ∧ 0 ≤ (θ ω).2.1 ∧ (θ ω).2.1 ≤ 1 ∧
      0 ≤ (θ ω).2.2 ∧ (θ ω).2.2 ≤ 1)
    (hden : ∀ ω, θ ω ∈ S ω →
      0 < (θ ω).1 * (θ ω).2.1 + (1 - (θ ω).1) * (1 - (θ ω).2.2)) :
    μ.real {ω | θ ω ∈ S ω} ≤ μ.real {ω | ppv (θ ω) ∈ T ω} := by
  apply measureReal_mono _ (measure_ne_top _ _)
  intro ω hω
  exact hcover ω ⟨θ ω, hω, rfl⟩

/-- The singleton parameter `(π, se, sp) = (1, 1, 1)` has PPV `1`
although its negative-test mass `(1 - π) * sp + π * (1 - se)` is zero:
a zero NPV denominator does not invalidate the PPV value. -/
theorem ppv_one_one_one :
    ppv (1, 1, 1) = 1 ∧ (1 - (1 : ℝ)) * 1 + 1 * (1 - 1) = 0 := by
  constructor <;> norm_num [ppv]

end MathlibExt.Biology.Diagnostics.BinaryObservation
