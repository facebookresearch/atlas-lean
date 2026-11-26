/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import MathlibExt.Analysis.ODE.ContinuumBalances
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

- `FluidDynamics.Traffic.VehicleAccounting.total_vehicle_change`:
  the telescoping accounting identity.
- `FluidDynamics.Traffic.VehicleAccounting.total_vehicle_change_eq_discrete`:
  the identity against the discrete-balance API.

## iii. Table of contents

- A. Vehicle accounting

## iv. References

- Standard finite-volume conservation accounting for cell
  transmission models.
-/

@[expose] public section

/-! ## A. Vehicle accounting -/

namespace FluidDynamics.Traffic.VehicleAccounting

/-- Vehicle accounting over a finite cell chain. Cells `0, ..., n-1`
have densities `k i` and face fluxes `F i` between cell `i - 1` and
cell `i` (with `F 0` the external inflow and `F n` the external
outflow). Under the conservative update
`k' i = k i + (dt / dx) * (F i - F (i + 1))`, the total vehicle
count changes by exactly `dt * (F 0 - F n)`: every internal face is
counted once as an outflow and once as an inflow, so only the two
external faces survive the telescoping sum. -/
theorem total_vehicle_change {n : ℕ} (k F : ℕ → ℝ) (dt dx : ℝ)
    (hdx : 0 < dx) :
    ∑ i ∈ Finset.range n,
        dx * ((k i + dt / dx * (F i - F (i + 1))) - k i)
      = dt * (F 0 - F n) := by
  have hdx' : dx ≠ 0 := ne_of_gt hdx
  have hterm : ∀ i : ℕ, dx * ((k i + dt / dx * (F i - F (i + 1))) - k i)
      = dt * (F i - F (i + 1)) := by
    intro i
    have key : dx * (dt / dx * (F i - F (i + 1))) = dt * (F i - F (i + 1)) := by
      rw [div_eq_mul_inv]
      have hring : dx * (dt * dx⁻¹ * (F i - F (i + 1)))
          = (dx * dx⁻¹) * (dt * (F i - F (i + 1))) := by ring
      rw [hring, mul_inv_cancel₀ hdx', one_mul]
    have hring2 : dx * (k i + dt / dx * (F i - F (i + 1)) - k i)
        = dx * (dt / dx * (F i - F (i + 1))) := by ring
    rw [hring2, key]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, hterm]
    ring

/-- The accounting identity in terms of the finite-volume
`totalDiscreteChange` API: the summed vehicle change is
`dx * dt` times the total discrete balance of the face fluxes
(the discrete balance is the per-unit-width boundary rate). -/
theorem total_vehicle_change_eq_discrete {n : ℕ} (k F : ℕ → ℝ)
    (dt dx : ℝ) (hdx : 0 < dx) :
    ∑ i ∈ Finset.range n,
        dx * ((k i + dt / dx * (F i - F (i + 1))) - k i)
      = dx * dt * MathlibExt.Analysis.ODE.ContinuumBalances.totalDiscreteChange ⟨dx, hdx⟩
          (fun j : Fin (n + 1) => F j.val) := by
  rw [total_vehicle_change k F dt dx hdx, MathlibExt.Analysis.ODE.ContinuumBalances.totalDiscreteChange_eq]
  have hdx' : dx ≠ 0 := ne_of_gt hdx
  field_simp
  have e1 : (Fin.last n).val = n := rfl
  have e2 : ((0 : Fin (n + 1))).val = 0 := rfl
  rw [e1, e2]
  ring

end FluidDynamics.Traffic.VehicleAccounting
