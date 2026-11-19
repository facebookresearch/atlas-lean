/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.SpaceSystems.MissionLedger

/-!
# Mission ledger checks

Concrete consumers of `PhyslibExt.SpaceSystems.MissionLedger`: initial stock `2` with flows
`+2, -3, +1` against capacities `4` and `3`, flows `-3, +3` with an infeasible middle step, and
two resources whose pooled total hides an infeasible one.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Schedules and capacities

## iv. References

None.

## A. Schedules and capacities

-/

open Finset MissionLedger

/-- Resources are not interchangeable: with initial stocks `2` and `5`, a draw of `3` from the
first resource and nothing from the second, the pooled stock stays in `[0, 20]` at both
prefixes, but the first resource falls to `-1`, below its floor `0`. -/
example :
    (∀ t ≤ 1, (0 : ℝ) ≤ ∑ i : Fin 2,
        stock (![2, 5] : Fin 2 → ℝ) ![fun _ => -3, fun _ => 0] i t ∧
      ∑ i : Fin 2, stock (![2, 5] : Fin 2 → ℝ) ![fun _ => -3, fun _ => 0] i t ≤ 20) ∧
    ¬ PrefixFeasible (fun _ => 0) (fun _ => 10) (fun _ => 0) (![2, 5] : Fin 2 → ℝ)
        ![fun _ => -3, fun _ => 0] 1 := by
  constructor
  · intro t ht
    have ht' : t = 0 ∨ t = 1 := by omega
    obtain rfl | rfl := ht'
    · constructor <;> norm_num [Fin.sum_univ_two, stock]
    · constructor <;> norm_num [Fin.sum_univ_two, stock, Finset.sum_range_succ]
  · intro h
    have h01 := h 0 1 le_rfl
    norm_num [stock, Finset.sum_range_succ] at h01

/-- Initial stock `2`, flows `+2, -3, +1`, floor `0`, no reserve: with any capacity of at
least `4` every prefix stock (`2, 4, 1, 2`) is feasible. -/
example (cap : ℝ) (hcap : 4 ≤ cap) :
    PrefixFeasible (fun _ : Unit => 0) (fun _ => cap) (fun _ => 0) (fun _ => 2)
      (fun _ => listFlow [2, -3, 1]) 3 := by
  intro i t ht
  have h0 : stock (fun _ : Unit => 2) (fun _ => listFlow [2, -3, 1]) i 0 = 2 := by
    norm_num [stock, listFlow]
  have h1 : stock (fun _ : Unit => 2) (fun _ => listFlow [2, -3, 1]) i 1 = 4 := by
    norm_num [stock, listFlow, Finset.sum_range_succ]
  have h2 : stock (fun _ : Unit => 2) (fun _ => listFlow [2, -3, 1]) i 2 = 1 := by
    norm_num [stock, listFlow, Finset.sum_range_succ]
  have h3 : stock (fun _ : Unit => 2) (fun _ => listFlow [2, -3, 1]) i 3 = 2 := by
    norm_num [stock, listFlow, Finset.sum_range_succ]
  have ht' : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 := by omega
  obtain rfl | rfl | rfl | rfl := ht'
  · rw [h0]; refine ⟨?_, ?_⟩ <;> simp only [] <;> linarith
  · rw [h1]; refine ⟨?_, ?_⟩ <;> simp only [] <;> linarith
  · rw [h2]; refine ⟨?_, ?_⟩ <;> simp only [] <;> linarith
  · rw [h3]; refine ⟨?_, ?_⟩ <;> simp only [] <;> linarith

/-- The same schedule with capacity `3` fails at the first step (prefix stock `4`), although
the final stock `2` lies in `[0, 3]`. -/
example :
    ¬ PrefixFeasible (fun _ : Unit => 0) (fun _ => 3) (fun _ => 0) (fun _ => 2)
        (fun _ => listFlow [2, -3, 1]) 3 ∧
      stock (fun _ : Unit => 2) (fun _ => listFlow [2, -3, 1]) () 1 = 4 ∧
      stock (fun _ : Unit => 2) (fun _ => listFlow [2, -3, 1]) () 3 = 2 := by
  have h1 : stock (fun _ : Unit => 2) (fun _ => listFlow [2, -3, 1]) () 1 = 4 := by
    norm_num [stock, listFlow, Finset.sum_range_succ]
  have h3 : stock (fun _ : Unit => 2) (fun _ => listFlow [2, -3, 1]) () 3 = 2 := by
    norm_num [stock, listFlow, Finset.sum_range_succ]
  refine ⟨?_, h1, h3⟩
  intro h
  have h01 := h () 1 (by norm_num)
  rw [h1] at h01
  norm_num at h01

/-- Initial stock `2` with flows `-3, +3` ends at `2`, inside `[0, 4]`, but the middle stock is
`-1`, so the schedule is not prefix feasible. -/
example :
    stock (fun _ : Unit => 2) (fun _ => listFlow [-3, 3]) () 2 = 2 ∧
      stock (fun _ : Unit => 2) (fun _ => listFlow [-3, 3]) () 1 = -1 ∧
      ¬ PrefixFeasible (fun _ : Unit => 0) (fun _ => 4) (fun _ => 0) (fun _ => 2)
        (fun _ => listFlow [-3, 3]) 2 := by
  have h2 : stock (fun _ : Unit => 2) (fun _ => listFlow [-3, 3]) () 2 = 2 := by
    norm_num [stock, listFlow, Finset.sum_range_succ]
  have h1 : stock (fun _ : Unit => 2) (fun _ => listFlow [-3, 3]) () 1 = -1 := by
    norm_num [stock, listFlow, Finset.sum_range_succ]
  refine ⟨h2, h1, ?_⟩
  intro h
  have h01 := h () 1 (by norm_num)
  rw [h1] at h01
  norm_num at h01
