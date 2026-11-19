/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Cell-transmission demand, supply, and face flux

## i. Overview

For the triangular fundamental diagram with capacity
`v * w * kj / (v + w)`, a cell's demand is `min (v * k, capacity)` and
its receiving supply is `min (w * (kj - k), capacity)`. The flux
through a face is the smaller of upstream demand and downstream
supply. On admissible densities the face flux is nonnegative and
bounded by both sides, and the capacity is attained at the critical
density.

## ii. Key results

- `FluidDynamics.Traffic.CellTransmission.faceFlux_nonneg_of_le`:
  nonnegativity on admissible densities.
- `FluidDynamics.Traffic.CellTransmission.faceFlux_le_demand`,
  `FluidDynamics.Traffic.CellTransmission.faceFlux_le_supply`: the
  two face bounds.
- `FluidDynamics.Traffic.CellTransmission.capacity_attained`:
  capacity attained at the critical density.

## iii. Table of contents

- A. Demand, supply, and face flux

## iv. References

- C. F. Daganzo, the cell transmission model, *Transportation
  Research B* 28(4), 1994.

## A. Demand, supply, and face flux
-/

@[expose] public section

namespace FluidDynamics.Traffic.CellTransmission

/-- Capacity of the triangular fundamental diagram with free-flow
speed `v`, wave speed `w`, jam density `kj`: the peak flow
`v * w * kj / (v + w)`, attained at the critical density. -/
noncomputable def capacity (v w kj : ℝ) : ℝ := v * w * kj / (v + w)

/-- Demand of a cell with density `k` under the triangular diagram:
free-flow flow capped at capacity. -/
noncomputable def demand (v w kj k : ℝ) : ℝ := min (v * k) (capacity v w kj)

/-- Receiving supply of a cell with density `k` under the triangular
diagram: congested-branch flow capped at capacity. -/
noncomputable def supply (v w kj k : ℝ) : ℝ :=
  min (w * (kj - k)) (capacity v w kj)

/-- Face flux between an upstream and downstream cell: the smaller of
upstream demand and downstream supply. -/
noncomputable def faceFlux (v w kj kup kdown : ℝ) : ℝ :=
  min (demand v w kj kup) (supply v w kj kdown)

/-- On admissible densities (`0 ≤ k ≤ kj` in both cells) with positive
speeds, the face flux is nonnegative. -/
theorem faceFlux_nonneg_of_le {v w kj kup kdown : ℝ}
    (hv : 0 < v) (hw : 0 < w) (hkj : 0 ≤ kj)
    (hup : 0 ≤ kup ∧ kup ≤ kj) (hdown : 0 ≤ kdown ∧ kdown ≤ kj) :
    0 ≤ faceFlux v w kj kup kdown := by
  have hcap : 0 ≤ capacity v w kj :=
    div_nonneg (mul_nonneg (mul_nonneg hv.le hw.le) hkj) (add_pos hv hw).le
  unfold faceFlux demand supply
  exact le_min (le_min (mul_nonneg hv.le hup.1) hcap)
    (le_min (mul_nonneg hw.le (sub_nonneg.mpr hdown.2)) hcap)

/-- The face flux never exceeds the upstream demand. -/
theorem faceFlux_le_demand {v w kj kup kdown : ℝ} :
    faceFlux v w kj kup kdown ≤ demand v w kj kup := by
  unfold faceFlux
  exact min_le_left _ _

/-- The face flux never exceeds the downstream receiving supply. -/
theorem faceFlux_le_supply {v w kj kup kdown : ℝ} :
    faceFlux v w kj kup kdown ≤ supply v w kj kdown := by
  unfold faceFlux
  exact min_le_right _ _

/-- Demand is nonnegative and capacity-bounded on admissible
densities. -/
theorem demand_nonneg_le {v w kj k : ℝ} (hv : 0 < v) (hw : 0 < w)
    (hkj : 0 ≤ kj) (hk : 0 ≤ k) :
    0 ≤ demand v w kj k ∧ demand v w kj k ≤ capacity v w kj := by
  have hcap : 0 ≤ capacity v w kj :=
    div_nonneg (mul_nonneg (mul_nonneg hv.le hw.le) hkj) (add_pos hv hw).le
  unfold demand
  exact ⟨le_min (mul_nonneg hv.le hk) hcap, min_le_right _ _⟩

/-- Supply is nonnegative and capacity-bounded on admissible
densities. -/
theorem supply_nonneg_le {v w kj k : ℝ} (hv : 0 < v) (hw : 0 < w)
    (hkj : 0 ≤ kj) (hk : k ≤ kj) :
    0 ≤ supply v w kj k ∧ supply v w kj k ≤ capacity v w kj := by
  have hcap : 0 ≤ capacity v w kj :=
    div_nonneg (mul_nonneg (mul_nonneg hv.le hw.le) hkj) (add_pos hv hw).le
  unfold supply
  exact ⟨le_min (mul_nonneg hw.le (sub_nonneg.mpr hk)) hcap, min_le_right _ _⟩

/-- The capacity is attained at the critical density
`kc = w * kj / (v + w)` from both branches. -/
theorem capacity_attained {v w kj : ℝ} (hv : 0 < v) (hw : 0 < w)
    (_hkj : 0 < kj) :
    demand v w kj (w * kj / (v + w)) = capacity v w kj
      ∧ supply v w kj (w * kj / (v + w)) = capacity v w kj := by
  have hvw : v + w ≠ 0 := ne_of_gt (add_pos hv hw)
  have hdem : v * (w * kj / (v + w)) = capacity v w kj := by
    unfold capacity
    field_simp
  have hsup : w * (kj - w * kj / (v + w)) = capacity v w kj := by
    unfold capacity
    field_simp
    ring
  constructor
  · unfold demand
    rw [hdem]
    exact min_self _
  · unfold supply
    rw [hsup]
    exact min_self _

end FluidDynamics.Traffic.CellTransmission
