/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Vehicle accounting over a finite cell chain

## i. Overview

Cells `0, ..., n - 1` carry densities `k i` and face fluxes `F i`
(`F 0` the external inflow, `F n` the external outflow). Under the
conservative update `k' i = k i + (dt / dx) * (F i - F (i + 1))`,
the total vehicle count changes by exactly `dt * (F 0 - F n)`:
each internal face is counted once as an outflow and once as an
inflow, so the sum telescopes to the two external faces.

## ii. Key results

- `total_vehicle_change`: the telescoping accounting identity.

## iii. Table of contents

- A. Vehicle accounting

## iv. References

- Standard finite-volume conservation accounting for cell
  transmission models.
-/

@[expose] public section

/-! ## A. Vehicle accounting -/

/-- Vehicle accounting over a finite cell chain. Cells `0, ..., n-1`
have densities `k i` and face fluxes `F i` between cell `i - 1` and
cell `i` (with `F 0` the external inflow and `F n` the external
outflow). Under the conservative update
`k' i = k i + (dt / dx) * (F i - F (i + 1))`, the total vehicle
count changes by exactly `dt * (F 0 - F n)`: every internal face is
counted once as an outflow and once as an inflow, so only the two
external faces survive the telescoping sum. -/
theorem total_vehicle_change {n : ℕ} (k F : ℕ → ℝ) (dt dx : ℝ)
    (hdx : dx ≠ 0) :
    ∑ i ∈ Finset.range n,
        dx * ((k i + dt / dx * (F i - F (i + 1))) - k i)
      = dt * (F 0 - F n) := by
  have h1 : ∀ i : ℕ,
      (k i + dt / dx * (F i - F (i + 1))) - k i
        = dt / dx * (F i - F (i + 1)) := by
    intro i
    ring
  have h3 : dx * (dt / dx) = dt := by
    rw [div_eq_mul_inv]
    calc dx * (dt * dx⁻¹)
        = dt * (dx * dx⁻¹) := by ring
      _ = dt * 1 := by rw [mul_inv_cancel₀ hdx]
      _ = dt := by ring
  have h : ∀ i : ℕ,
      dx * ((k i + dt / dx * (F i - F (i + 1))) - k i)
        = dt * (F i - F (i + 1)) := by
    intro i
    calc dx * ((k i + dt / dx * (F i - F (i + 1))) - k i)
        = dx * (dt / dx * (F i - F (i + 1))) := by rw [h1]
      _ = (dx * (dt / dx)) * (F i - F (i + 1)) := by rw [← mul_assoc]
      _ = dt * (F i - F (i + 1)) := by rw [h3]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, h]
    ring
