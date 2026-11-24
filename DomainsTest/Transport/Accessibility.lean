/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum

import Domains.Transport.Accessibility

/-!
# Threshold accessibility checks

Focused checks for `MathlibExt.Transport.Accessibility`: one
destination with opportunity `5` and travel time `2` contributes `0` at
threshold `1` and `5` at threshold `3`; a missing travel time always
contributes zero.

These are elaboration and non-vacuity checks, not new results.
-/

open TransportAccessibility

/-- Contribution below and above the travel time. -/
example : thresholdContribution (fun _ : Fin 1 => (5 : ℝ))
      (fun _ => some (2 : NNReal)) (1 : NNReal) 0 = 0
    ∧ thresholdContribution (fun _ : Fin 1 => (5 : ℝ))
      (fun _ => some (2 : NNReal)) (3 : NNReal) 0 = 5 :=
  ⟨thresholdContribution_eq_zero_of_gt _ _ _ rfl (by norm_num),
    thresholdContribution_of_le _ _ _ rfl (by norm_num)⟩

/-- The aggregate sum at thresholds below and above the travel time,
and its monotonicity, through the public API. -/
example : thresholdOpportunitySum ({0} : Finset (Fin 1)) (fun _ : Fin 1 => (5 : ℝ))
      (fun _ => some (2 : NNReal)) (1 : NNReal) = 0
    ∧ thresholdOpportunitySum ({0} : Finset (Fin 1)) (fun _ : Fin 1 => (5 : ℝ))
      (fun _ => some (2 : NNReal)) (3 : NNReal) = 5
    ∧ thresholdOpportunitySum ({0} : Finset (Fin 1)) (fun _ : Fin 1 => (5 : ℝ))
      (fun _ => some (2 : NNReal)) (1 : NNReal)
      ≤ thresholdOpportunitySum ({0} : Finset (Fin 1)) (fun _ : Fin 1 => (5 : ℝ))
      (fun _ => some (2 : NNReal)) (3 : NNReal) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [thresholdOpportunitySum, thresholdContribution]
  · simp only [thresholdOpportunitySum, thresholdContribution]
    rw [if_pos (by norm_num : (2 : NNReal) ≤ 3), Finset.sum_singleton]
  · exact thresholdOpportunitySum_mono _ _ _ (by intro i _; norm_num) (by norm_num)

/-- Missing travel time contributes zero. -/
example : thresholdContribution (fun _ : Fin 1 => (5 : ℝ))
      (fun _ => none) (3 : NNReal) 0 = 0 :=
  thresholdContribution_eq_zero_of_eq_none _ _ _ rfl
