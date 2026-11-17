/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.HeatTransfer.EnergySourceRemoval
import Mathlib.Tactic.NormNum

/-!
# Slab and cylinder heat-removal checks

Concrete consumers of `PhyslibExt.HeatTransfer.EnergySourceRemoval`:
the numeric slab `Ts = Tb = 300`, `L = 2`, `k = 2`, `H = 8` with
midplane `302` and total outward removal `16`, the source-free
branch `H = 0`, and the numeric heated cylinder with outward power
`32π`.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Numeric slab with source
- B. Source-free branch
- C. Numeric heated cylinder

## iv. References

- `PhyslibExt.HeatTransfer.EnergySourceRemoval`
-/

/-- Outward fluxes for the numeric slab: left outward flux
`k * T'(0) = 8`, right outward flux `-k * T'(2) = 8`, sum `16 = H * L`. -/
example : 2 * HeatTransfer.slabGradient 300 300 2 2 8 0 = 8 ∧
    -(2 * HeatTransfer.slabGradient 300 300 2 2 8 2) = 8 ∧
      2 * HeatTransfer.slabGradient 300 300 2 2 8 0 -
        2 * HeatTransfer.slabGradient 300 300 2 2 8 2 = 8 * 2 := by
  refine ⟨by norm_num [HeatTransfer.slabGradient],
    by norm_num [HeatTransfer.slabGradient], ?_⟩
  have h := HeatTransfer.outwardFluxSum (Ts := 300) (Tb := 300) (L := 2)
    (k := 2) (H := 8) (by norm_num)
  norm_num at h ⊢
  exact h

/-- Midplane temperature of the numeric slab: `302`. -/
example : HeatTransfer.slabTemperature 300 300 2 2 8 1 = 302 := by
  have h := HeatTransfer.slabTemperature_midplane (Ts := 300) (L := 2)
    (k := 2) (H := 8) (by norm_num)
  norm_num at h
  exact h

/-- Source cutoff: with `H = 0` and equal surfaces the steady profile is
the constant surface temperature (a steady branch, not a transient). -/
example (d : ℝ) : HeatTransfer.slabTemperature 300 300 2 2 0 d = 300 := by
  simp [HeatTransfer.slabTemperature]

/-- Numeric heated cylinder `Ts = 300`, `R = 2`, `k = 2`, `qvol = 8`:
center `304`, surface `300`, rise `4`, zero center gradient, and the
radial equation value `-4` at `r = 1`. -/
example : HeatTransfer.cylinderTemperature 300 2 2 8 0 = 304 ∧
    HeatTransfer.cylinderTemperature 300 2 2 8 2 = 300 ∧
      HeatTransfer.cylinderGradient 2 8 0 = 0 ∧
        (1 / (1 : ℝ)) * deriv (fun s : ℝ =>
          s * HeatTransfer.cylinderGradient 2 8 s) 1 = -4 := by
  refine ⟨by norm_num [HeatTransfer.cylinderTemperature],
    by norm_num [HeatTransfer.cylinderTemperature],
    HeatTransfer.cylinderGradient_zero 2 8, ?_⟩
  have h := HeatTransfer.cylinder_radial_equation (k := 2) (qvol := 8)
    (r := 1) (by norm_num) (by norm_num)
  rw [show (1 : ℝ) / 1 = 1 from by norm_num, one_mul]
  norm_num at h
  exact h

/-- Outward power per unit length of the numeric cylinder:
`2πR * (-k * T'(R)) = 32π` at `R = 2`, `k = 2`, `qvol = 8`. -/
example : 2 * Real.pi * 2 * (-2 * HeatTransfer.cylinderGradient 2 8 2) =
    32 * Real.pi := by
  have h := HeatTransfer.cylinder_outwardPower (R := 2) (k := 2)
    (qvol := 8) (by norm_num)
  calc 2 * Real.pi * 2 * (-2 * HeatTransfer.cylinderGradient 2 8 2)
      = Real.pi * 2 ^ 2 * 8 := h
    _ = 32 * Real.pi := by ring
