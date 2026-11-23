/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.LinearReservoirEnvelope
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Linear-reservoir envelope checks

Concrete consumers of `PhyslibExt.EarthScience.LinearReservoirEnvelope`
for `I = 3`, `k = 1 / 2`, hence steady storage `I / k = 6`: initial
storage below, equal to, and above steady storage; the dry interval
`I = 0`; capacity endpoints; and the `k = 0` and `t < 0` controls.

## i. Overview

These are elaboration and non-vacuity checks for the transported
envelope results, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Steady-storage sides and endpoints
- B. Capacity and invalid controls

## iv. References

- `PhyslibExt.EarthScience.LinearReservoirEnvelope`
-/

open EarthScience

/-! ## A. Steady-storage sides and endpoints -/

/-- Below steady storage: `S0 = 2 ≤ 6` stays at most `6` and nonnegative. -/
example : linearReservoirStorage 3 (1 / 2) 2 2 ≤ 6 := by
  have h := linearReservoirStorage_le_steady (I := 3) (k := 1 / 2)
    (S0 := 2) (t := 2) (by norm_num) (by norm_num)
  norm_num at h
  exact h

example : 0 ≤ linearReservoirStorage 3 (1 / 2) 2 2 :=
  linearReservoirStorage_nonneg (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- Equal to steady storage: `S0 = 6` is constant. -/
example : linearReservoirStorage 3 (1 / 2) 6 2 = 6 := by
  norm_num [linearReservoirStorage]

example : linearReservoirStorage 3 (1 / 2) 6 2 ≤ 6
    ∧ 6 ≤ linearReservoirStorage 3 (1 / 2) 6 2 := by
  constructor
  · have h := linearReservoirStorage_le_steady (I := 3) (k := 1 / 2)
      (S0 := 6) (t := 2) (by norm_num) (by norm_num)
    norm_num at h
    exact h
  · have h := steady_le_linearReservoirStorage (I := 3) (k := 1 / 2)
      (S0 := 6) (t := 2) (by norm_num) (by norm_num)
    norm_num at h
    exact h

/-- Above steady storage: `S0 = 10` stays at least `6`. -/
example : 6 ≤ linearReservoirStorage 3 (1 / 2) 10 2 := by
  have h := steady_le_linearReservoirStorage (I := 3) (k := 1 / 2)
    (S0 := 10) (t := 2) (by norm_num) (by norm_num)
  norm_num at h
  exact h

/-- At `t = 0` the profile is the initial storage. -/
example : linearReservoirStorage 3 (1 / 2) 10 0 = 10 :=
  storage_initial 3 (1 / 2) 10

/-- Dry interval: `I = 0` still gives nonnegative decaying storage. -/
example : 0 ≤ linearReservoirStorage 0 (1 / 2) 10 2 :=
  linearReservoirStorage_nonneg (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-! ## B. Capacity and invalid controls -/

/-- Capacity endpoint at `t = 0`: `S0 = Smax = 10` is attained and allowed. -/
example : linearReservoirStorage 3 (1 / 2) 10 0 = 10
    ∧ linearReservoirStorage 3 (1 / 2) 10 0 ≤ 10 :=
  ⟨storage_initial 3 (1 / 2) 10,
    linearReservoirStorage_le_capacity (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)⟩

/-- Capacity with `S0 = I / k = Smax = 6`: storage is `6` at every time. -/
example (t : ℝ) : linearReservoirStorage 3 (1 / 2) 6 t = 6 := by
  norm_num [linearReservoirStorage]

example : linearReservoirStorage 3 (1 / 2) 10 2 ≤ 10 :=
  linearReservoirStorage_le_capacity (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- The bridge guard `k ≠ 0` is necessary: at `k = 0` the reservoir
profile is `0` here while the compartment amount is `1`. -/
example : linearReservoirStorage 1 0 0 1
    ≠ MathlibExt.Biology.Biophysics.CompartmentKinetics.amount 0 1 0 1 := by
  rw [MathlibExt.Biology.Biophysics.CompartmentKinetics.amount_rate_zero]
  norm_num [linearReservoirStorage]

/-- The capacity hypothesis `0 ≤ t` is necessary: at `t = -1` the
profile starting at `Smax = 10` exceeds the envelope. -/
example : ¬ linearReservoirStorage 3 (1 / 2) 10 (-1) ≤ 10 := by
  have hval : linearReservoirStorage 3 (1 / 2) 10 (-1)
      = 6 + 4 * Real.exp (1 / 2) := by
    norm_num [linearReservoirStorage]
  have hexp : (1 : ℝ) < Real.exp (1 / 2) :=
    Real.one_lt_exp_iff.mpr (by norm_num)
  intro h
  rw [hval] at h
  linarith

#print axioms EarthScience.linearReservoirStorage_eq_amount
#print axioms EarthScience.linearReservoirStorage_nonneg
#print axioms EarthScience.linearReservoirStorage_le_steady
#print axioms EarthScience.steady_le_linearReservoirStorage
#print axioms EarthScience.linearReservoirStorage_le_capacity
