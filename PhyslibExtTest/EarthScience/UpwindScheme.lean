/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.UpwindScheme

/-!
# Upwind-update checks

Concrete consumers of `PhyslibExt.EarthScience.UpwindScheme`: a two-cell
update at `ν = 1/2`, the CFL violation at `ν = 2`, and the one-cell
periodic case.

## i. Overview

These are elaboration and non-vacuity checks, not new results. With two
cells `c = (1, 0)` at `ν = 1/2`, the update is `(1/2, 1/2)` with the same
total `1`. At `ν = 2` the first cell goes negative, so nonnegativity
fails. With one cell the update is the identity.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Two-cell update at CFL `1/2`
- B. CFL violation and the one-cell case

## iv. References

- `PhyslibExt.EarthScience.UpwindScheme`
-/

/-- Two-cell update at `ν = 1/2`: every updated cell is nonnegative. -/
example (i : ZMod 2) :
    0 ≤ (1 - 1 / 2) * (if i = 0 then (1 : ℝ) else 0) +
      (1 / 2) * (if i - 1 = 0 then (1 : ℝ) else 0) :=
  EarthScience.upwind_nonneg (1 / 2) (by exact div_nonneg zero_le_one (by norm_num : (0:ℝ) ≤ 2)) (by rw [div_le_one (by norm_num : (0:ℝ) < 2)]; norm_num)
    (fun i => if i = 0 then 1 else 0) (fun i => by split <;> norm_num) i

/-- Two-cell update at `ν = 1/2`: the total sum is preserved. -/
example :
    ∑ i : ZMod 2, ((1 - 1 / 2) * (if i = 0 then (1 : ℝ) else 0) +
      (1 / 2) * (if i - 1 = 0 then (1 : ℝ) else 0)) =
      ∑ i : ZMod 2, (if i = 0 then (1 : ℝ) else 0) :=
  EarthScience.upwind_sum_eq (1 / 2) (fun i => if i = 0 then 1 else 0)

/-- CFL violation: at `ν = 2` the cell `0` goes to `-1`, so the updated
field is not everywhere nonnegative. -/
example : ¬ ∀ i : ZMod 2, 0 ≤ (1 - 2) * (if i = 0 then (1 : ℝ) else 0) +
    2 * (if i - 1 = 0 then (1 : ℝ) else 0) := by
  intro h
  have h0 := h 0
  have hsub : (0 : ZMod 2) - 1 = 1 := by decide
  rw [hsub] at h0
  simp at h0

/-- One cell: the periodic update is the identity for every `ν`. -/
example (ν : ℝ) (x : ℝ) :
    ∑ i : ZMod 1, ((1 - ν) * (if i = 0 then x else 0) +
      ν * (if i - 1 = 0 then x else 0)) = x := by
  rw [EarthScience.upwind_sum_eq,
    Finset.sum_eq_single 0 (fun i _ hi => ite_eq_right hi) (fun h => absurd (Finset.mem_univ 0) h)]
  simp only [ite_true]
