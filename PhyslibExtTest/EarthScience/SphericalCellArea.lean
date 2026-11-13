/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.SphericalCellArea

/-!
# Spherical cell area checks

Concrete consumers of `PhyslibExt.EarthScience.SphericalCellArea`.

## i. Overview

Concrete case with one latitude band `φ = [-π/2, π/2]` (`n = 1`),
`m = 4` longitude cells, `R = 2`: the cell areas are
`4 * (1 - (-1)) * (2π / 4) = 4π` each, and the four cells sum to
`16π = 4π R²`. The constant case `C = 3` gives `48π`.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Concrete and boundary checks

## iv. References

- `PhyslibExt.EarthScience.SphericalCellArea`
-/

/-- One latitude band, four longitude cells, `R = 2`: total area `16π`. -/
example : ∑ i : Fin 1, ∑ _j : Fin 4,
    (2 : ℝ) ^ 2 * (Real.sin ((![-(Real.pi / 2), Real.pi / 2] : Fin 2 → ℝ) i.succ) -
      Real.sin ((![-(Real.pi / 2), Real.pi / 2] : Fin 2 → ℝ) i.castSucc)) *
    (2 * Real.pi / (4 : ℕ)) = 4 * Real.pi * (2 : ℝ) ^ 2 := by
  have hφ : (![-(Real.pi / 2), Real.pi / 2] : Fin 2 → ℝ) 0 = -(Real.pi / 2) := by simp
  have hlast : (![-(Real.pi / 2), Real.pi / 2] : Fin 2 → ℝ) (Fin.last 1) = Real.pi / 2 := by
    simp [Fin.last]
  exact EarthScience.spherical_cell_area_sum (n := 1) (m := 4) (by norm_num)
    (φ := ![-(Real.pi / 2), Real.pi / 2]) hφ hlast

/-- Constant case: `C = 3` gives `3 * 16π`. -/
example : ∑ i : Fin 1, ∑ _j : Fin 4,
    (((2 : ℝ) ^ 2 * (Real.sin ((![-(Real.pi / 2), Real.pi / 2] : Fin 2 → ℝ) i.succ) -
      Real.sin ((![-(Real.pi / 2), Real.pi / 2] : Fin 2 → ℝ) i.castSucc)) *
    (2 * Real.pi / (4 : ℕ))) * 3) = 3 * (4 * Real.pi * (2 : ℝ) ^ 2) := by
  have hφ : (![-(Real.pi / 2), Real.pi / 2] : Fin 2 → ℝ) 0 = -(Real.pi / 2) := by simp
  have hlast : (![-(Real.pi / 2), Real.pi / 2] : Fin 2 → ℝ) (Fin.last 1) = Real.pi / 2 := by
    simp [Fin.last]
  exact EarthScience.spherical_cell_area_integrates_constant (n := 1) (m := 4) (by norm_num)
    (φ := ![-(Real.pi / 2), Real.pi / 2]) hφ hlast

/-- Boundary case `m = 1`: a single longitude cell has area `4π R²`. -/
example : ∑ i : Fin 1, ∑ _j : Fin 1,
    (2 : ℝ) ^ 2 * (Real.sin ((![-(Real.pi / 2), Real.pi / 2] : Fin 2 → ℝ) i.succ) -
      Real.sin ((![-(Real.pi / 2), Real.pi / 2] : Fin 2 → ℝ) i.castSucc)) *
    (2 * Real.pi / (1 : ℕ)) = 4 * Real.pi * (2 : ℝ) ^ 2 := by
  have hφ : (![-(Real.pi / 2), Real.pi / 2] : Fin 2 → ℝ) 0 = -(Real.pi / 2) := by simp
  have hlast : (![-(Real.pi / 2), Real.pi / 2] : Fin 2 → ℝ) (Fin.last 1) = Real.pi / 2 := by
    simp [Fin.last]
  exact EarthScience.spherical_cell_area_sum (n := 1) (m := 1) (by norm_num)
    (φ := ![-(Real.pi / 2), Real.pi / 2]) hφ hlast
