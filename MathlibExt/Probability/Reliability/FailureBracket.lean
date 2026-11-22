/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.OuterMeasure.AE

/-!
# Distribution-free failure-probability bracket

If two variables satisfy `|g - L| ≤ delta` on an event `B`, then the
failure probability of `g` is bracketed by that of `L` shifted by
`delta`, up to the exceptional probability of `Bᶜ`:
`P (L ≤ -delta) - P (Bᶜ) ≤ P (g ≤ 0) ≤ P (L ≤ delta) + P (Bᶜ)`.
The theorems are stated as two inequalities for an arbitrary measure
(no measurability or distribution assumption); the corollary combines
them in subtracted (truncated) form. Equality counts as failure,
matching `MathlibExt.Probability.Reliability.LimitState`.

## Main results

* `Reliability.measure_failure_bracket_upper` and
  `Reliability.measure_failure_bracket_lower`: the two sides.
* `Reliability.measure_failure_bracket`: the subtracted bracket for an
  arbitrary measure.
-/

@[expose] public section

namespace Reliability

open MeasureTheory Set

/-- Distribution-free error bracket, upper side: if `|g - L| ≤ delta` on
an event `B`, then `P (g ≤ 0) ≤ P (L ≤ delta) + P (Bᶜ)`, with no
measurability or distribution assumption. -/
theorem measure_failure_bracket_upper {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (g L : Ω → ℝ) (B : Set Ω) (delta : ℝ)
    (h : ∀ ω : Ω, ω ∈ B → |g ω - L ω| ≤ delta) :
    μ {ω : Ω | g ω ≤ 0} ≤ μ {ω : Ω | L ω ≤ delta} + μ Bᶜ := by
  calc μ {ω : Ω | g ω ≤ 0}
      ≤ μ ({ω : Ω | L ω ≤ delta} ∪ Bᶜ) := by
        apply measure_mono
        intro ω hω
        simp only [Set.mem_ofPred_eq] at hω
        by_cases hB : ω ∈ B
        · have habs := h ω hB
          rw [abs_le] at habs
          simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_compl_iff]
          left
          linarith [habs.1, habs.2]
        · simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_compl_iff]
          right
          exact hB
    _ ≤ μ {ω : Ω | L ω ≤ delta} + μ Bᶜ := measure_union_le _ _

/-- Distribution-free error bracket, lower side: under the same premise,
`P (L ≤ -delta) ≤ P (g ≤ 0) + P (Bᶜ)`. -/
theorem measure_failure_bracket_lower {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (g L : Ω → ℝ) (B : Set Ω) (delta : ℝ)
    (h : ∀ ω : Ω, ω ∈ B → |g ω - L ω| ≤ delta) :
    μ {ω : Ω | L ω ≤ -delta} ≤ μ {ω : Ω | g ω ≤ 0} + μ Bᶜ := by
  calc μ {ω : Ω | L ω ≤ -delta}
      ≤ μ ({ω : Ω | g ω ≤ 0} ∪ Bᶜ) := by
        apply measure_mono
        intro ω hω
        simp only [Set.mem_ofPred_eq] at hω
        by_cases hB : ω ∈ B
        · have habs := h ω hB
          rw [abs_le] at habs
          simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_compl_iff]
          left
          linarith [habs.1, habs.2]
        · simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_compl_iff]
          right
          exact hB
    _ ≤ μ {ω : Ω | g ω ≤ 0} + μ Bᶜ := measure_union_le _ _
/-- The bracket in subtracted form, for an arbitrary measure:
`μ (L ≤ -delta) - μ Bᶜ ≤ μ (g ≤ 0) ≤ μ (L ≤ delta) + μ Bᶜ` in `ℝ≥0∞`
truncated subtraction. -/
theorem measure_failure_bracket {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (g L : Ω → ℝ) (B : Set Ω)
    (delta : ℝ) (h : ∀ ω : Ω, ω ∈ B → |g ω - L ω| ≤ delta) :
    μ {ω : Ω | L ω ≤ -delta} - μ Bᶜ ≤ μ {ω : Ω | g ω ≤ 0}
      ∧ μ {ω : Ω | g ω ≤ 0} ≤ μ {ω : Ω | L ω ≤ delta} + μ Bᶜ :=
  ⟨tsub_le_iff_right.mpr (measure_failure_bracket_lower μ g L B delta h),
    measure_failure_bracket_upper μ g L B delta h⟩

end Reliability
