/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Economics.Actuarial.LastSurvivorAnnuity
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Tactic.NormNum

/-! # Two lives subject to the same random outcome -/

open Actuarial MeasureTheory ProbabilityTheory MathlibExt.Economics.Finance
open scoped NNReal

private noncomputable def third : unitInterval := ⟨1 / 3, by constructor <;> norm_num⟩
private noncomputable abbrev law := bernoulliMeasure true false third

-- Outcome true (mass 1/3): deaths at 3 and 2; false (mass 2/3): deaths at 1 and 3.
private def x : Bool → ℝ≥0 | true => 3 | false => 1
private def y : Bool → ℝ≥0 | true => 2 | false => 3

-- At time 2 exactly one life survives. Multiplying the marginals would charge for a
-- joint-life payment in a state in which none is due.
example : law.real {ω | 2 < min (x ω) (y ω)} = 0 ∧
    law.real {ω | 2 < x ω} * law.real {ω | 2 < y ω} = 2 / 9 := by
  classical
  norm_num [law, bernoulliMeasure_real_apply, MeasurableSet.of_discrete, x, y, third,
    unitInterval.toNNReal, unitInterval.symm]

private noncomputable def benefit (k : ℕ) : ℝ := if k = 1 then 4 else 6
private noncomputable def discount (k : ℕ) : ℝ := if k = 1 then 3 / 4 else 1 / 3
private noncomputable def value (T : Bool → ℝ≥0) : ℝ :=
  lifeAnnuityValue law {1, 2} (fun k ↦ k) benefit discount T

-- Discounted benefits are 3 and 2. Compute the four values directly from the two outcomes.
example : value x = 5 / 3 ∧ value y = 13 / 3 ∧
    value (fun ω ↦ min (x ω) (y ω)) = 1 ∧ value (fun ω ↦ max (x ω) (y ω)) = 5 := by
  norm_num [value, lifeAnnuityValue, law, integral_bernoulliMeasure, presentValue, third,
    benefit, discount, Set.indicator_apply, x, y, smul_eq_mul]

-- The abstract identity applies to these dependent lives with no extra hypothesis on their law.
example : value (fun ω ↦ max (x ω) (y ω)) =
    value x + value y - value (fun ω ↦ min (x ω) (y ω)) :=
  lifeAnnuityValue_max _ _ _ _ _ Measurable.of_discrete Measurable.of_discrete

-- Strict survival excludes the instalment even for certain death exactly at a noninteger date.
example : lifeAnnuityValue law {0} (fun _ ↦ 1 / 2) (fun _ ↦ 7) (fun _ ↦ 1)
    (fun _ ↦ 1 / 2) = 0 := by
  simp [lifeAnnuityValue, presentValue]

example (P : Measure Bool) (date : ℕ → ℝ≥0) (c d : ℕ → ℝ) (T : Bool → ℝ≥0) :
    lifeAnnuityValue P ∅ date c d T = 0 := by
  simp [lifeAnnuityValue, presentValue]
