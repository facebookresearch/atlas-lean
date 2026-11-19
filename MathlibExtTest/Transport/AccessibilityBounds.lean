/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Transport.AccessibilityBounds
import Mathlib.Tactic.NormNum

/-!
# Accessibility-bounds checks

Focused checks for `MathlibExt.Transport.AccessibilityBounds`:
zero opportunities give zero accessibility, and accessibility is
monotone on a two-destination example.

These are elaboration and non-vacuity checks, not new results.
-/

open TransportAccessibility

/-- Zero opportunities give zero accessibility: the sum is bounded
below by 0 and above by the total, which is 0. -/
example : thresholdOpportunitySum ({0, 1} : Finset ℕ)
    (fun _ => (0 : ℝ)) (fun _ => some 1) 2 = 0 := by
  apply le_antisymm
  · have h := thresholdOpportunitySum_le_total ({0, 1} : Finset ℕ)
      (fun _ => (0 : ℝ)) (fun _ => some 1) 2 (by simp)
    simpa using h
  · exact thresholdOpportunitySum_nonneg ({0, 1} : Finset ℕ)
      (fun _ => (0 : ℝ)) (fun _ => some 1) 2 (by simp)

/-- Monotonicity on a concrete two-destination example. -/
example : thresholdOpportunitySum ({0, 1} : Finset ℕ)
    (fun i => (i : ℝ)) (fun _ => some 1) 2
    ≤ thresholdOpportunitySum ({0, 1} : Finset ℕ)
      (fun i => (i : ℝ) + 1) (fun _ => some 1) 2 :=
  thresholdOpportunitySum_mono_opportunities ({0, 1} : Finset ℕ)
    (fun i => (i : ℝ)) (fun i => (i : ℝ) + 1) (fun _ => some 1) 2
    (by intro i _; exact le_add_of_nonneg_right zero_le_one)
