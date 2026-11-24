/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.Approximation.UnrelatedMachinesRounding
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum

/-! # Tests for rounding schedules on unrelated parallel machines -/

open Finset MathlibExt.ComputerScience.UnrelatedMachinesRoundingWanted

-- A job of length two fits fractional deadlines of one when split between two machines.
-- Its assigned machine must exceed that deadline.
example : ∃ σ : Unit → Bool, (∀ i, ∑ j with σ j = i, 2 ≤ 1 + 2) ∧
    1 < ∑ j with σ j = σ (), 2 := by
  obtain ⟨σ, _, hload⟩ := exists_assignment_load_le
    (fun (_ : Bool) (_ : Unit) => 2) (fun _ => 1) 2 (fun _ _ => 1 / 2)
    (by intros; norm_num) (by simp) (by intro; norm_num [Fintype.sum_bool])
    (by intro; norm_num)
  exact ⟨σ, hload, by simp⟩

-- With zero cutoff, a positive processing time rules out that machine even for a single job.
example : ∃ σ : Unit → Bool, σ () = true := by
  let p (i : Bool) (_ : Unit) : ℕ := if i then 0 else 1
  let x (i : Bool) (_ : Unit) : ℝ := if i then 1 else 0
  obtain ⟨σ, helig, _⟩ := exists_assignment_load_le p (fun _ => 0) 0 x
    (by intro i j; cases i <;> simp [x]) (by intro i j; cases i <;> simp [p, x])
    (by simp [x]) (by intro i; cases i <;> simp [p, x])
  refine ⟨σ, ?_⟩
  cases h : σ () with
  | false => simpa [p, h] using helig ()
  | true => rfl
