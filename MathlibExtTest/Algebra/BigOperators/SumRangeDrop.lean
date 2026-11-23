/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

import MathlibExt.Algebra.BigOperators.SumRangeDrop

/-!
# Series-drop checks

Concrete consumers of `MathlibExt.Algebra.BigOperators.SumRangeDrop`: unit
resistances and flow `5` starting at potential `100` give the chain
`100, 95, 90`, a total drop of `10`, and recovered flow `5`.

These are elaboration and non-vacuity checks, not new results.
-/

open MathlibExt

/-- The drop hypothesis for the two-step unit-resistance chain. -/
private theorem unitChain_drop :
    ∀ i : ℕ, i < 2 →
      (fun j : ℕ => 100 - 5 * (j : ℝ)) i
        - (fun j : ℕ => 100 - 5 * (j : ℝ)) (i + 1)
      = 5 * (fun _ : ℕ => (1 : ℝ)) i := by
  intro i hi
  interval_cases i <;> norm_num

/-- Reconstruction and the total drop on the two-step unit chain. -/
example :
    (fun j : ℕ => 100 - 5 * (j : ℝ)) 2 = 90
      ∧ (100 - 5 * (0 : ℝ)) - (100 - 5 * (2 : ℝ)) = 10 := by
  have hrec := apply_eq_sub_mul_sum_range (n := 2) (j := 2) (q := (5 : ℝ))
    (R := fun _ : ℕ => (1 : ℝ)) (P := fun j : ℕ => 100 - 5 * (j : ℝ))
    (by norm_num) unitChain_drop
  have htot := sub_eq_mul_sum_range (n := 2) (q := (5 : ℝ))
    (R := fun _ : ℕ => (1 : ℝ)) (P := fun j : ℕ => 100 - 5 * (j : ℝ))
    unitChain_drop
  refine ⟨?_, ?_⟩ <;> norm_num [Finset.sum_range_succ] at hrec htot ⊢

/-- Flow recovery on the same chain: `10 / 2`. -/
example : (5 : ℝ) = 10 / 2 := by
  have h := eq_div_sum_range (n := 2) (q := (5 : ℝ))
    (R := fun _ : ℕ => (1 : ℝ)) (P := fun j : ℕ => 100 - 5 * (j : ℝ))
    (by norm_num) (fun _ _ => one_pos) unitChain_drop
  norm_num [Finset.sum_range_succ] at h
  linarith
