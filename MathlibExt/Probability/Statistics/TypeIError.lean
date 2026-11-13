/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultipleTesting.Basic
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Type-I error of a calibrated rejection rule

Two rejection rules and their type-I error bounds under the null law:
rejecting when a valid (super-uniform) p-value is at most `α`, and
rejecting when a test statistic with calibrated null law falls in a
rejection set of null probability at most `α`. A p-value with the
uniform law on `[0, 1]` under the null is valid, so the p-value rule
applies to it. The critical-value bound is stated in `ℝ≥0∞`, so an
infinite null mass cannot read as a zero type-I error. Concrete instances
at levels `1 / 10` and `9 / 10` are in
`MathlibExtTest.Probability.Statistics.TypeIError` (Atlas roadmap
ST02.T04).
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.TypeIError

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open MathlibExt.Probability.Statistics.MultipleTesting

/-- **Type-I error of a p-value rejection rule (ST02.T04).** Rejecting
exactly when `p ≤ α`, with `p` a valid p-value under the null law `μ`,
has type-I error at most `α`: the type-I error is `μ.real {p ≤ α}`.
This is the type-I-error framing of `valid_measureReal_le`, cited
verbatim here; its proof is not redone. No finiteness assumption on `μ`
is needed. -/
theorem typeI_error_le_of_isValidPValue {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {p : Ω → ℝ}
    (hvalid : IsValidPValue μ p) {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    μ.real {ω | p ω ≤ α} ≤ α :=
  valid_measureReal_le hvalid hα.1 hα.2

/-- **Type-I error of a calibrated critical-value rule (ST02.T04).** If the
test statistic `T` has the calibrated null law `ν` under `P` and the
rejection set `R` has `ν`-probability at most `α`, then rejecting exactly
when `T ∈ R` has type-I error at most `α` (via `HasLaw.measure_eq`).
Probabilities and the level are in `ℝ≥0∞`: under `Measure.real` an
infinite mass would read as `0`. -/
theorem typeI_error_le_of_hasLaw {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] {P : Measure Ω} {T : Ω → X} {ν : Measure X}
    (hT : HasLaw T ν P) {R : Set X} (hR : MeasurableSet R)
    {α : ℝ≥0∞} (hcal : ν R ≤ α) :
    P (T ⁻¹' R) ≤ α := by
  have hmeas : MeasurableSet {x | x ∈ R} := by simpa using hR
  change P {ω | T ω ∈ R} ≤ α
  rw [hT.measure_eq hmeas, Set.ofPred_mem_eq]
  exact hcal

/-- **Calibrated uniform p-value rule.** A p-value with the uniform law on
`[0, 1]` under the null is valid, so rejecting when `p ≤ α` has type-I
error at most `α`. -/
theorem typeI_error_le_of_hasLaw_uniform_pValue {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {p : Ω → ℝ}
    (hp : HasLaw p (volume.restrict (Set.Icc (0 : ℝ) 1)) μ)
    {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    μ.real {ω | p ω ≤ α} ≤ α :=
  valid_measureReal_le (isValidPValue_of_hasLaw_uniform hp) hα.1 hα.2

end MathlibExt.Probability.Statistics.TypeIError
