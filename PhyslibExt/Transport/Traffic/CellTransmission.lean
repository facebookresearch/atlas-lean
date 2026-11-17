/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Cell-transmission demand, supply, and face flux

## i. Overview

For the triangular fundamental diagram, a cell's demand is
`min (v * k, Qmax)` and its receiving supply is
`min (w * (kj - k), Qmax)`. The flux through a face is the smaller of
upstream demand and downstream supply. On admissible densities the
face flux is nonnegative and bounded by both sides.

## ii. Key results

- `CellTransmission.faceFlux_nonneg_of_le`: nonnegativity on
  admissible densities.
- `CellTransmission.faceFlux_le_demand`,
  `CellTransmission.faceFlux_le_supply`: the two face bounds.
- `CellTransmission.demand_nonneg_le`,
  `CellTransmission.supply_nonneg_le`: demand and supply bounds.

## iii. Table of contents

- A. Demand, supply, and face flux

## iv. References

- C. F. Daganzo, the cell transmission model, *Transportation
  Research B* 28(4), 1994.

## A. Demand, supply, and face flux
-/

@[expose] public section

namespace CellTransmission

/-- Triangular-fundamental-diagram demand of a cell with density `k`,
free-flow speed `v`, capacity `Qmax`: `min (v * k) Qmax`. -/
noncomputable def demand (v Qmax k : ℝ) : ℝ := min (v * k) Qmax

/-- Receiving supply of a cell with density `k`, wave speed `w`, jam
density `kj`, capacity `Qmax`: `min (w * (kj - k)) Qmax`. -/
noncomputable def supply (w Qmax kj k : ℝ) : ℝ := min (w * (kj - k)) Qmax

/-- Face flux between an upstream and downstream cell: the smaller of
upstream demand and downstream supply. -/
noncomputable def faceFlux (v w Qmax kj kup kdown : ℝ) : ℝ :=
  min (demand v Qmax kup) (supply w Qmax kj kdown)

/-- On admissible densities (`0 ≤ k ≤ kj` in both cells) with positive
speeds and nonnegative capacity, the face flux is nonnegative and
bounded by both the local demand and the receiving supply. -/
theorem faceFlux_nonneg_of_le {v w Qmax kj kup kdown : ℝ}
    (hv : 0 < v) (hw : 0 < w) (hQ : 0 ≤ Qmax)
    (hup : 0 ≤ kup ∧ kup ≤ kj) (hdown : 0 ≤ kdown ∧ kdown ≤ kj) :
    0 ≤ faceFlux v w Qmax kj kup kdown := by
  unfold faceFlux demand supply
  exact le_min (le_min (mul_nonneg hv.le hup.1) hQ)
    (le_min (mul_nonneg hw.le (sub_nonneg.mpr hdown.2)) hQ)

/-- The face flux never exceeds the upstream demand. -/
theorem faceFlux_le_demand {v w Qmax kj kup kdown : ℝ} :
    faceFlux v w Qmax kj kup kdown ≤ demand v Qmax kup := by
  unfold faceFlux
  exact min_le_left _ _

/-- The face flux never exceeds the downstream receiving supply. -/
theorem faceFlux_le_supply {v w Qmax kj kup kdown : ℝ} :
    faceFlux v w Qmax kj kup kdown ≤ supply w Qmax kj kdown := by
  unfold faceFlux
  exact min_le_right _ _

/-- Demand itself is nonnegative and capacity-bounded on admissible
densities. -/
theorem demand_nonneg_le {v Qmax k : ℝ} (hv : 0 < v) (hQ : 0 ≤ Qmax)
    (hk : 0 ≤ k) : 0 ≤ demand v Qmax k ∧ demand v Qmax k ≤ Qmax := by
  constructor
  · unfold demand
    exact le_min (mul_nonneg hv.le hk) hQ
  · unfold demand
    exact min_le_right _ _

/-- Supply itself is nonnegative and capacity-bounded on admissible
densities. -/
theorem supply_nonneg_le {w Qmax kj k : ℝ} (hw : 0 < w) (hQ : 0 ≤ Qmax)
    (hk : k ≤ kj) : 0 ≤ supply w Qmax kj k ∧ supply w Qmax kj k ≤ Qmax := by
  constructor
  · unfold supply
    exact le_min (mul_nonneg hw.le (sub_nonneg.mpr hk)) hQ
  · unfold supply
    exact min_le_right _ _

end CellTransmission
