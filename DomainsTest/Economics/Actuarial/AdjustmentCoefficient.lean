/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Economics.Actuarial.AdjustmentCoefficient

/-!
# Tests for the adjustment coefficient

With unit claims and unit arrival rate, the premium `exp 1 - 1` makes `1` an exact root.
Shortening the interval to end at that root leaves no positive root in its interior.
-/

open Actuarial MeasureTheory ProbabilityTheory Real Set

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

private noncomputable abbrev unitGap := adjustmentGap (fun _ : Ω ↦ (1 : ℝ)) μ 1 (exp 1 - 1)

private theorem unitGap_eq (r : ℝ) : unitGap μ r = exp r - 1 - (exp 1 - 1) * r := by
  simp [unitGap, adjustmentGap]

private theorem unitClaim_crossing :
    unitGap μ 1 = 0 ∧ (∀ r ∈ Ioo (0 : ℝ) 2, unitGap μ r = 0 → r = 1) ∧
      (∀ r ∈ Ioo (0 : ℝ) 1, unitGap μ r < 0) ∧ (∀ r ∈ Ioc (1 : ℝ) 2, 0 < unitGap μ r) := by
  have he := Real.add_one_lt_exp (one_ne_zero : (1 : ℝ) ≠ 0)
  have hone : unitGap μ 1 = 0 := by simp [unitGap_eq]
  have htwo : 0 < unitGap μ 2 := by
    rw [unitGap_eq, show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [sq_pos_of_pos (show 0 < exp 1 - 1 by linarith)]
  obtain ⟨R, _, _, hu, hl, hr⟩ := exists_adjustmentCoefficient (μ := μ)
    (X := fun _ ↦ (1 : ℝ)) (rate := 1) (c := exp 1 - 1) (r₀ := 2)
    (by simp) (by simp) zero_lt_one (by simpa using (show 1 < exp 1 - 1 by linarith))
    (by norm_num) (integrable_const _) htwo
  obtain rfl := hu 1 (by constructor <;> norm_num) hone
  exact ⟨hone, hu, hl, hr⟩

example : unitGap μ 0 = 0 ∧ ¬ ∃ r ∈ Ioo (0 : ℝ) 1, unitGap μ r = 0 := by
  refine ⟨by simp [unitGap_eq], ?_⟩
  rintro ⟨r, hr, hz⟩
  exact ((unitClaim_crossing μ).2.2.1 r hr).ne hz
