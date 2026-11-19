/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.FluidDynamics.Traffic.CellTransmission
import Mathlib.Tactic

/-!
# Cell-transmission invariant density interval

## i. Overview

One explicit cell-transmission update step,
`k + (dt / dx) * (F_in - F_out)` with face fluxes
`FluidDynamics.Traffic.CellTransmission.faceFlux`, preserves the
admissible density interval `[0, kj]` under the CFL condition
`(dt / dx) * max v w ≤ 1`: the outflow cannot drain the cell below
zero (it is bounded by the demand `v * k`), and the inflow cannot
overfill it (it is bounded by the supply `w * (kj - k)`).

## ii. Key results

- `FluidDynamics.Traffic.CellTransmission.update_mem_Icc`:
  invariance of the admissible density interval.

## iii. Table of contents

- A. Invariance of the density interval

## iv. References

- C. F. Daganzo, *The cell transmission model: A dynamic
  representation of highway traffic consistent with the
  hydrodynamic theory*, Transportation Research Part B, 1994.
-/

@[expose] public section

namespace FluidDynamics.Traffic.CellTransmission

/-! ## A. Invariance of the density interval -/

/-- One cell-transmission update step preserves the admissible
density interval `[0, kj]` under the CFL condition. -/
theorem update_mem_Icc {v w kj k kin kout dt dx : ℝ} (hv : 0 < v)
    (hw : 0 < w) (hkj : 0 < kj) (hk : 0 ≤ k ∧ k ≤ kj)
    (hkin : 0 ≤ kin ∧ kin ≤ kj) (hkout : 0 ≤ kout ∧ kout ≤ kj)
    (hdt : 0 ≤ dt) (hdx : 0 < dx) (hCFL : (dt / dx) * max v w ≤ 1) :
    0 ≤ k + (dt / dx) * (faceFlux v w kj kin k
        - faceFlux v w kj k kout)
      ∧ k + (dt / dx) * (faceFlux v w kj kin k
        - faceFlux v w kj k kout) ≤ kj := by
  have hr : 0 ≤ dt / dx := div_nonneg hdt hdx.le
  have hFout_le : faceFlux v w kj k kout ≤ v * k :=
    le_trans faceFlux_le_demand (by unfold demand; exact min_le_left _ _)
  have hFin_le : faceFlux v w kj kin k ≤ w * (kj - k) :=
    le_trans faceFlux_le_supply (by unfold supply; exact min_le_left _ _)
  have hFout_nn : 0 ≤ faceFlux v w kj k kout :=
    faceFlux_nonneg_of_le hv hw hkj.le hk hkout
  have hFin_nn : 0 ≤ faceFlux v w kj kin k :=
    faceFlux_nonneg_of_le hv hw hkj.le hkin hk
  have hrv : (dt / dx) * v ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_left (le_max_left v w) hr) hCFL
  have hrw : (dt / dx) * w ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_left (le_max_right v w) hr) hCFL
  constructor
  · nlinarith [mul_nonneg hr hFin_nn,
      mul_nonneg hr (sub_nonneg.mpr hFout_le),
      mul_nonneg (sub_nonneg.mpr hrv) hk.1]
  · nlinarith [mul_nonneg hr hFout_nn,
      mul_nonneg hr (sub_nonneg.mpr hFin_le),
      mul_nonneg (sub_nonneg.mpr hrw) (sub_nonneg.mpr hk.2)]

end FluidDynamics.Traffic.CellTransmission
