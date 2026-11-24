/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.StorageCapacity
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Storage-capacity checks

Concrete consumers of
`PhyslibExt.EarthScience.StorageCapacity`: interest-first
deficit then surplus (storage falls then refills with spill),
an infeasible capacity, pure spill, and the empty horizon.

## i. Overview

These are elaboration and sign checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Drawdown, refill, and spill
- B. Infeasibility and the empty horizon

## iv. References

- `PhyslibExt.EarthScience.StorageCapacity`
-/

open List
open EarthScience

namespace PhyslibExtTest.EarthScience.StorageCapacity

/-- Trajectory for releases `![3, 0]`, inflows `![0, 5]`,
capacity `4`: storage `4, 1, 4`. -/
private def traj : ℕ → ℝ
  | 0 => 4
  | 1 => 1
  | _ => 4

private theorem traj_step : ∀ t (ht : t < 2),
    traj (t + 1)
      = min 4 (traj t + (![0, 5] : Fin 2 → ℝ) ⟨t, ht⟩
          - (![3, 0] : Fin 2 → ℝ) ⟨t, ht⟩) := by
  intro t ht
  interval_cases t <;> norm_num [traj]

/-! ## A. Drawdown, refill, and spill -/

private theorem k_one :
    requiredStorageAt (![3, 0] : Fin 2 → ℝ) ![0, 5] 1 = 3 := by
  change requiredStorageAt (![3, 0] : Fin 2 → ℝ) ![0, 5] (0 + 1)
    = 3
  rw [requiredStorageAt_succ _ _ (by norm_num),
    requiredStorageAt_zero]
  norm_num

private theorem k_two :
    requiredStorageAt (![3, 0] : Fin 2 → ℝ) ![0, 5] 2 = 0 := by
  change requiredStorageAt (![3, 0] : Fin 2 → ℝ) ![0, 5] (1 + 1)
    = 0
  rw [requiredStorageAt_succ _ _ (by norm_num), k_one]
  norm_num

/-- The trajectory is capacity minus the deficit walk:
`K 1 = 3`, `K 2 = 0`. -/
example : traj 1 = 4 - requiredStorageAt ![3, 0] ![0, 5] 1
    ∧ traj 2 = 4 - requiredStorageAt ![3, 0] ![0, 5] 2 :=
  ⟨storage_eq_capacity_sub_requiredStorageAt ![3, 0] ![0, 5] 4
      traj rfl traj_step 1 (by norm_num),
    storage_eq_capacity_sub_requiredStorageAt ![3, 0] ![0, 5] 4
      traj rfl traj_step 2 (by norm_num)⟩

/-- Pure spill: inflow `5`, no release, capacity `2` stays
full. -/
example : requiredStorageAt (![0] : Fin 1 → ℝ) ![5] 1 = 0 := by
  change requiredStorageAt (![0] : Fin 1 → ℝ) ![5] (0 + 1) = 0
  rw [requiredStorageAt_succ _ _ (by norm_num),
    requiredStorageAt_zero]
  norm_num

/-- The drawdown/refill trajectory is feasible. -/
example : ∀ t ≤ 2, 0 ≤ traj t := by
  have hworst : worstRequiredStorage (![3, 0] : Fin 2 → ℝ)
      ![0, 5] ≤ 4 := by
    obtain ⟨u, hu2, hu⟩ :=
      (requiredStorageAt_le_worst_and_exists_eq
        (![3, 0] : Fin 2 → ℝ) ![0, 5]).2
    interval_cases u
    · rw [requiredStorageAt_zero] at hu
      linarith
    · rw [k_one] at hu
      linarith
    · rw [k_two] at hu
      linarith
  exact (storage_feasible_iff ![3, 0] ![0, 5] 4 traj rfl
    traj_step).mpr hworst

/-! ## B. Infeasibility and the empty horizon -/

/-- Capacity `2` is infeasible for the same data: at `t = 1`
storage is `2 - 3 = -1`. -/
example : ¬ ∀ t ≤ 2,
    0 ≤ (fun t => 2 - requiredStorageAt (![3, 0] : Fin 2 → ℝ)
      ![0, 5] t) t := by
  intro h
  have h1 := h 1 (by norm_num)
  simp only [] at h1
  rw [k_one] at h1
  norm_num at h1

/-- Empty horizon: the worst required storage is `0`, so
zero capacity is feasible and required. -/
example : worstRequiredStorage (![] : Fin 0 → ℝ) ![] = 0 := by
  have hge : (0 : ℝ)
      ≤ worstRequiredStorage (![] : Fin 0 → ℝ) ![] := by
    have h := (requiredStorageAt_le_worst_and_exists_eq
      (![] : Fin 0 → ℝ) ![]).1 0
    rwa [requiredStorageAt_zero] at h
  have hle : worstRequiredStorage (![] : Fin 0 → ℝ) ![]
      ≤ 0 := by
    have h := (storage_feasible_iff (![] : Fin 0 → ℝ) ![] 0
      (fun _ => 0) rfl
      (fun t ht => absurd ht (Nat.not_lt_zero t))).mp
    exact h (fun t _ => le_refl 0)
  linarith

#print axioms EarthScience.storage_eq_capacity_sub_requiredStorageAt
#print axioms EarthScience.storage_feasible_iff

end PhyslibExtTest.EarthScience.StorageCapacity
