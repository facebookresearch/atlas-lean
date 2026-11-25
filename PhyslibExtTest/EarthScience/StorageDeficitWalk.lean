/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.StorageDeficitWalk
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Sequent-peak storage deficit checks

Concrete consumers of `PhyslibExt.EarthScience.StorageDeficitWalk`:
mixed-sign deficits `d = [3, -3, 4]` with storage deficits
`K = 0, 3, 0, 4` and worst `4`, the empty horizon, and an
all-negative deficit sequence whose maximum is the empty
suffix (zero).

## i. Overview

These are elaboration and sign checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Mixed-sign deficits
- B. Empty horizon and maximum-includes-zero

## iv. References

- `PhyslibExt.EarthScience.StorageDeficitWalk`
-/

open EarthScience

namespace PhyslibExtTest.EarthScience.StorageDeficitWalk

/-! ## A. Mixed-sign deficits -/

/-- `K₀ = 0`, `K₁ = 3`, `K₂ = 0`, `K₃ = 4` for `d = [3, -3, 4]`,
by the one-step reflected update. -/
example : requiredStorageAt ![3, 0, 4] ![0, 3, 0] 0 = 0 :=
  requiredStorageAt_zero _ _

private theorem k_one :
    requiredStorageAt ![3, 0, 4] ![0, 3, 0] 1 = 3 := by
  change requiredStorageAt ![3, 0, 4] ![0, 3, 0] (0 + 1) = 3
  rw [requiredStorageAt_succ _ _ (by norm_num : (0 : ℕ) < 3),
    requiredStorageAt_zero]
  norm_num

private theorem k_two :
    requiredStorageAt ![3, 0, 4] ![0, 3, 0] 2 = 0 := by
  change requiredStorageAt ![3, 0, 4] ![0, 3, 0] (1 + 1) = 0
  rw [requiredStorageAt_succ _ _ (by norm_num : (1 : ℕ) < 3), k_one]
  norm_num

private theorem k_three :
    requiredStorageAt ![3, 0, 4] ![0, 3, 0] 3 = 4 := by
  change requiredStorageAt ![3, 0, 4] ![0, 3, 0] (2 + 1) = 4
  rw [requiredStorageAt_succ _ _ (by norm_num : (2 : ℕ) < 3), k_two]
  norm_num

example : requiredStorageAt ![3, 0, 4] ![0, 3, 0] 1 = 3 := k_one

example : requiredStorageAt ![3, 0, 4] ![0, 3, 0] 2 = 0 := k_two

example : requiredStorageAt ![3, 0, 4] ![0, 3, 0] 3 = 4 := k_three

/-- The worst-required storage is attained (at `t = 3` it is
at least `4`). -/
example : ∃ t ≤ 3, requiredStorageAt ![3, 0, 4] ![0, 3, 0] t
    = worstRequiredStorage ![3, 0, 4] ![0, 3, 0] :=
  (requiredStorageAt_le_worst_and_exists_eq _ _).2

example : (4 : ℝ) ≤ worstRequiredStorage ![3, 0, 4] ![0, 3, 0] := by
  have h := (requiredStorageAt_le_worst_and_exists_eq
    ![3, 0, 4] ![0, 3, 0]).1 3
  rwa [k_three] at h

/-- Suffix agreement at the focused data: some final window
attains `K₃`, and every final window is at most `K₃`. -/
example : ∃ i ≤ 3, suffixDeficitSum ![3, 0, 4] ![0, 3, 0] i 3
    = requiredStorageAt ![3, 0, 4] ![0, 3, 0] 3 :=
  exists_suffixDeficitSum_eq_requiredStorageAt _ _ (by norm_num)

example : suffixDeficitSum ![3, 0, 4] ![0, 3, 0] 0 3
    ≤ requiredStorageAt ![3, 0, 4] ![0, 3, 0] 3 :=
  suffixDeficitSum_le_requiredStorageAt _ _ (by norm_num) (by norm_num)

/-- Terminal deficit below the peak: for releases `[3, 0]` and
inflows `[0, 5]`, the reservoir refills, so the terminal deficit
is `0` while the worst-required storage is at least `3`. -/
example : terminalStorageDeficit ![3, 0] ![0, 5]
    < worstRequiredStorage ![3, 0] ![0, 5] := by
  have hk1 : requiredStorageAt ![3, 0] ![0, 5] 1 = 3 := by
    change requiredStorageAt ![3, 0] ![0, 5] (0 + 1) = 3
    rw [requiredStorageAt_succ _ _ (by norm_num : (0 : ℕ) < 2),
      requiredStorageAt_zero]
    norm_num
  have hk2 : requiredStorageAt ![3, 0] ![0, 5] 2 = 0 := by
    change requiredStorageAt ![3, 0] ![0, 5] (1 + 1) = 0
    rw [requiredStorageAt_succ _ _ (by norm_num : (1 : ℕ) < 2), hk1]
    norm_num
  have hworst := (requiredStorageAt_le_worst_and_exists_eq
    ![3, 0] ![0, 5]).1 1
  rw [hk1] at hworst
  rw [terminalStorageDeficit_eq_at_length, hk2]
  linarith

/-! ## B. Empty horizon and maximum-includes-zero -/

/-- Empty horizon: no deficit, no worst-case storage. -/
example : requiredStorageAt (![] : Fin 0 → ℝ) ![] 0 = 0 :=
  requiredStorageAt_zero _ _

example : worstRequiredStorage (![] : Fin 0 → ℝ) ![] = 0 := by
  obtain ⟨t, ht, he⟩ :=
    (requiredStorageAt_le_worst_and_exists_eq
      (![] : Fin 0 → ℝ) ![]).2
  have ht0 : t = 0 := by omega
  rw [ht0, requiredStorageAt_zero] at he
  exact he.symm

/-- All-negative deficits `d = [-1, -2]`: the deficit stays at
zero, attained by the empty suffix. -/
private theorem n_one :
    requiredStorageAt ![0, 0] ![1, 2] 1 = 0 := by
  change requiredStorageAt ![0, 0] ![1, 2] (0 + 1) = 0
  rw [requiredStorageAt_succ _ _ (by norm_num : (0 : ℕ) < 2),
    requiredStorageAt_zero]
  norm_num

example : requiredStorageAt ![0, 0] ![1, 2] 2 = 0 := by
  change requiredStorageAt ![0, 0] ![1, 2] (1 + 1) = 0
  rw [requiredStorageAt_succ _ _ (by norm_num : (1 : ℕ) < 2), n_one]
  norm_num

example : suffixDeficitSum ![0, 0] ![1, 2] 2 2 = 0 :=
  suffixDeficitSum_self _ _ 2

example : 0 ≤ requiredStorageAt ![0, 0] ![1, 2] 2 :=
  requiredStorageAt_nonneg _ _ 2

#print axioms EarthScience.requiredStorageAt_zero
#print axioms EarthScience.requiredStorageAt_succ
#print axioms EarthScience.terminalStorageDeficit_eq_at_length
#print axioms EarthScience.requiredStorageAt_eq_walkMax_reverse
#print axioms EarthScience.suffixDeficitSum_le_requiredStorageAt
#print axioms EarthScience.exists_suffixDeficitSum_eq_requiredStorageAt
#print axioms EarthScience.suffixDeficitSum_self
#print axioms EarthScience.requiredStorageAt_nonneg
#print axioms EarthScience.requiredStorageAt_le_worst_and_exists_eq

end PhyslibExtTest.EarthScience.StorageDeficitWalk
