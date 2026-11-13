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
`16π = 4π R²`. The constant case `C = 3` gives `48π`. A two-band
partition `φ = [-π/2, 0, π/2]` exercises the partition theorem. The
non-monotone endpoint sequence `φ = [-π/2, π/2, -π/2, π/2]` is not a
partition: its middle signed weight is `-4π`, and its weights still sum to
`4π` by the signed-weight lemma.

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
  exact EarthScience.signed_band_weight_sum (n := 1) (m := 4) (by norm_num)
    (φ := ![-(Real.pi / 2), Real.pi / 2]) hφ hlast

/-- Constant case: `C = 3` gives `3 * 16π`. -/
example : ∑ i : Fin 1, ∑ _j : Fin 4,
    (((2 : ℝ) ^ 2 * (Real.sin ((![-(Real.pi / 2), Real.pi / 2] : Fin 2 → ℝ) i.succ) -
      Real.sin ((![-(Real.pi / 2), Real.pi / 2] : Fin 2 → ℝ) i.castSucc)) *
    (2 * Real.pi / (4 : ℕ))) * 3) = 3 * (4 * Real.pi * (2 : ℝ) ^ 2) := by
  have hφ : (![-(Real.pi / 2), Real.pi / 2] : Fin 2 → ℝ) 0 = -(Real.pi / 2) := by simp
  have hlast : (![-(Real.pi / 2), Real.pi / 2] : Fin 2 → ℝ) (Fin.last 1) = Real.pi / 2 := by
    simp [Fin.last]
  exact EarthScience.signed_band_weight_sum_mul_const (n := 1) (m := 4) (by norm_num)
    (φ := ![-(Real.pi / 2), Real.pi / 2]) hφ hlast

/-- Boundary case `m = 1`: a single longitude cell has area `4π R²`. -/
example : ∑ i : Fin 1, ∑ _j : Fin 1,
    (2 : ℝ) ^ 2 * (Real.sin ((![-(Real.pi / 2), Real.pi / 2] : Fin 2 → ℝ) i.succ) -
      Real.sin ((![-(Real.pi / 2), Real.pi / 2] : Fin 2 → ℝ) i.castSucc)) *
    (2 * Real.pi / (1 : ℕ)) = 4 * Real.pi * (2 : ℝ) ^ 2 := by
  have hφ : (![-(Real.pi / 2), Real.pi / 2] : Fin 2 → ℝ) 0 = -(Real.pi / 2) := by simp
  have hlast : (![-(Real.pi / 2), Real.pi / 2] : Fin 2 → ℝ) (Fin.last 1) = Real.pi / 2 := by
    simp [Fin.last]
  exact EarthScience.signed_band_weight_sum (n := 1) (m := 1) (by norm_num)
    (φ := ![-(Real.pi / 2), Real.pi / 2]) hφ hlast

/-- The two-band partition `[-π/2, 0, π/2]` with four longitude cells and `R = 1`: every cell
area is nonnegative and the areas sum to `4π`. -/
example :
    (∀ i : Fin 2, 0 ≤ (1 : ℝ) ^ 2 *
        (Real.sin ((![-(Real.pi / 2), 0, Real.pi / 2] : Fin 3 → ℝ) i.succ) -
          Real.sin ((![-(Real.pi / 2), 0, Real.pi / 2] : Fin 3 → ℝ) i.castSucc)) *
        (2 * Real.pi / (4 : ℕ))) ∧
      ∑ i : Fin 2, ∑ _j : Fin 4, (1 : ℝ) ^ 2 *
        (Real.sin ((![-(Real.pi / 2), 0, Real.pi / 2] : Fin 3 → ℝ) i.succ) -
          Real.sin ((![-(Real.pi / 2), 0, Real.pi / 2] : Fin 3 → ℝ) i.castSucc)) *
        (2 * Real.pi / (4 : ℕ)) = 4 * Real.pi * (1 : ℝ) ^ 2 := by
  have hmono : StrictMono (![-(Real.pi / 2), 0, Real.pi / 2] : Fin 3 → ℝ) := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i <;> simp <;> linarith [Real.pi_pos]
  exact EarthScience.spherical_cell_area_sum (n := 2) (m := 4) (by norm_num)
    (![-(Real.pi / 2), 0, Real.pi / 2]) hmono (by simp) (by simp [Fin.last])

/-- The endpoint sequence `[-π/2, π/2, -π/2, π/2]` is not a latitude partition, so the partition
theorem does not apply to it. -/
example : ¬ StrictMono
    (![-(Real.pi / 2), Real.pi / 2, -(Real.pi / 2), Real.pi / 2] : Fin 4 → ℝ) := by
  intro h
  have h12 := h (show (1 : Fin 4) < 2 by decide)
  simp at h12
  linarith [Real.pi_pos]

/-- Its middle signed weight (`R = 1`, `m = 1`) is `-4π`, not an area. -/
example : (1 : ℝ) ^ 2 *
    (Real.sin ((![-(Real.pi / 2), Real.pi / 2, -(Real.pi / 2), Real.pi / 2] : Fin 4 → ℝ)
        (1 : Fin 3).succ) -
      Real.sin ((![-(Real.pi / 2), Real.pi / 2, -(Real.pi / 2), Real.pi / 2] : Fin 4 → ℝ)
        (1 : Fin 3).castSucc)) * (2 * Real.pi / (1 : ℕ)) = -(4 * Real.pi) := by
  simp
  ring

/-- Its signed weights still sum to `4π`, by the signed-weight lemma. -/
example : ∑ i : Fin 3, ∑ _j : Fin 1, (1 : ℝ) ^ 2 *
    (Real.sin ((![-(Real.pi / 2), Real.pi / 2, -(Real.pi / 2), Real.pi / 2] : Fin 4 → ℝ)
        i.succ) -
      Real.sin ((![-(Real.pi / 2), Real.pi / 2, -(Real.pi / 2), Real.pi / 2] : Fin 4 → ℝ)
        i.castSucc)) * (2 * Real.pi / (1 : ℕ)) = 4 * Real.pi * (1 : ℝ) ^ 2 :=
  EarthScience.signed_band_weight_sum (n := 3) (m := 1) (by norm_num)
    (![-(Real.pi / 2), Real.pi / 2, -(Real.pi / 2), Real.pi / 2]) (by simp) (by simp [Fin.last])
