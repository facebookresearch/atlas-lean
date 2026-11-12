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
applies to it. Concrete instances at levels `1 / 10` and `9 / 10` are
proved as `*_example` theorems (Atlas roadmap ST02.T04).
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.TypeIError

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.Statistics.MultipleTesting

/-- **Type-I error of a p-value rejection rule (ST02.T04).** Rejecting
exactly when `p ≤ α`, with `p` a valid p-value under the null law `μ`,
has type-I error at most `α`: the type-I error is `μ.real {p ≤ α}`.
This is the type-I-error framing of `valid_measureReal_le`, cited
verbatim here; its proof is not redone. The `IsFiniteMeasure` binder
is retained verbatim from the frozen pinned statement (the comparator
requires an exact statement match); the proof does not use it. -/
theorem typeI_error_le_of_isValidPValue {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {p : Ω → ℝ}
    (hvalid : IsValidPValue μ p) {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    μ.real {ω | p ω ≤ α} ≤ α :=
  valid_measureReal_le hvalid hα.1 hα.2

/-- **Type-I error of a calibrated critical-value rule (ST02.T04).** If the
test statistic `T` has the calibrated null law `ν` under `P` and the
rejection set `R` has `ν`-probability at most `α`, then rejecting exactly
when `T ∈ R` has type-I error at most `α` (via `HasLaw.measureReal_eq`). -/
theorem typeI_error_le_of_hasLaw {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] {P : Measure Ω} {T : Ω → X} {ν : Measure X}
    (hT : HasLaw T ν P) {R : Set X} (hR : MeasurableSet R)
    {α : ℝ} (hcal : ν.real R ≤ α) :
    P.real (T ⁻¹' R) ≤ α := by
  have hmeas : MeasurableSet {x | x ∈ R} := by simpa using hR
  change P.real {ω | T ω ∈ R} ≤ α
  rw [hT.measureReal_eq hmeas, Set.ofPred_mem_eq]
  exact hcal

/-- **Calibrated uniform p-value rule.** A p-value with the uniform law on
`[0, 1]` under the null is valid, so rejecting when `p ≤ α` has type-I
error at most `α`. -/
theorem typeI_error_le_of_hasLaw_uniform_pValue {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {p : Ω → ℝ}
    (hp : HasLaw p (volume.restrict (Set.Icc (0 : ℝ) 1)) μ)
    {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    μ.real {ω | p ω ≤ α} ≤ α := by
  exact typeI_error_le_of_isValidPValue (isValidPValue_of_hasLaw_uniform hp) hα

/-- Concrete test: the identity p-value under the uniform law on `[0, 1]`
rejects with type-I error at most `1 / 10` at level `1 / 10`. -/
theorem typeI_error_uniform_example :
    (volume.restrict (Set.Icc (0 : ℝ) 1)).real {x : ℝ | x ≤ (1 / 10 : ℝ)} ≤
      (1 / 10 : ℝ) := by
  have : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    constructor
    simp [Real.volume_Icc]
  have h := typeI_error_le_of_hasLaw_uniform_pValue (p := id) HasLaw.id
    (α := (1 / 10 : ℝ)) (by norm_num)
  simpa using h

/-- Concrete test: the critical-value rule rejecting when the statistic
is at most `9 / 10` under the uniform law has type-I error at most
`9 / 10` (via the calibrated set `Iic (9 / 10)`). -/
theorem typeI_error_critical_value_example :
    (volume.restrict (Set.Icc (0 : ℝ) 1)).real
      ((fun x : ℝ => x) ⁻¹' Set.Iic (9 / 10 : ℝ)) ≤ (9 / 10 : ℝ) := by
  have hset : Set.Iic (9 / 10 : ℝ) ∩ Set.Icc (0 : ℝ) 1 = Set.Icc (0 : ℝ) (9 / 10) := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.2.1, hx.1⟩
    · intro hx
      exact ⟨hx.2, hx.1, by linarith [hx.2]⟩
  have hcal : (volume.restrict (Set.Icc (0 : ℝ) 1)).real (Set.Iic (9 / 10 : ℝ)) ≤
      (9 / 10 : ℝ) := by
    have heq : (volume.restrict (Set.Icc (0 : ℝ) 1)).real (Set.Iic (9 / 10 : ℝ)) =
        (9 / 10 : ℝ) := by
      rw [measureReal_def, Measure.restrict_apply measurableSet_Iic, hset, Real.volume_Icc,
        sub_zero, ENNReal.toReal_ofReal (by norm_num)]
    exact heq.le
  have h := typeI_error_le_of_hasLaw (T := (fun x : ℝ => x))
    (R := Set.Iic (9 / 10 : ℝ)) HasLaw.id measurableSet_Iic (α := (9 / 10 : ℝ)) hcal
  exact h

end MathlibExt.Probability.Statistics.TypeIError
