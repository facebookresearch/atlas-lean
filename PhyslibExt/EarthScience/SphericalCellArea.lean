/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open Finset

/-!
# Spherical cell area weights

For a latitude partition `phi` of `[-pi/2, pi/2]` with `n` latitude bands
and `m` longitude cells, the cell area for band `i` and longitude cell
`j` is `R^2 (sin phi_{i+1} - sin phi_i) (2 pi / m)`. Summing over `i`
telescopes to `sin(pi/2) - sin(-pi/2) = 2`, and summing over the `m`
longitude cells gives `2 pi`, so the total is the sphere area
`4 pi R^2`. The same weights integrate a constant `C` to
`C * 4 pi R^2`: the weights integrate a constant to the correct total
area.

## i. Overview

The inner sum over longitude cells is constant in `j`, giving a factor
`m`. The latitude sum telescopes. The constant-integration theorem
factors `C` out of the double sum and uses the first theorem.

## ii. Key results

- `EarthScience.spherical_cell_area_sum`: cell areas sum to `4 pi R^2`.
- `EarthScience.spherical_cell_area_integrates_constant`: weighted sum
  of a constant is `C * 4 pi R^2`.

## iii. Table of contents

- A. Spherical cell area weights

## iv. References

- `Finset.sum_const`, `Finset.card_univ` in Mathlib.
- `Real.sin_pi_div_two`, `Real.sin_neg` in Mathlib.

## A. Spherical cell area weights
-/

@[expose] public section

namespace EarthScience

private theorem telescope_sum_sub : ∀ (n : ℕ) (s : Fin (n + 1) → ℝ),
    ∑ i : Fin n, (s i.succ - s i.castSucc) = s (Fin.last n) - s 0 := by
  intro n
  induction n with
  | zero =>
      intro s
      simp [Fin.last_zero]
  | succ n ih =>
      intro s
      rw [Fin.sum_univ_castSucc (fun i : Fin (n + 1) => s i.succ - s i.castSucc)]
      simp only [Fin.succ_castSucc]
      have h2 : ∑ i : Fin n, (s (i.succ.castSucc) - s (i.castSucc.castSucc))
          = s ((Fin.last n).castSucc) - s (Fin.castSucc 0) :=
        ih (fun k : Fin (n + 1) => s k.castSucc)
      rw [Fin.castSucc_zero] at h2
      rw [h2, Fin.succ_last]
      change s ((Fin.last n).castSucc) - s 0
        + (s (Fin.last (n + 1)) - s ((Fin.last n).castSucc))
        = s (Fin.last (n + 1)) - s 0
      ring

set_option linter.unusedVariables false in
/-- Spherical cell area weights: for a latitude partition `φ` of
`[-π/2, π/2]` with `m` longitude cells, the sum of the cell areas
`R² (sin φ_{i+1} - sin φ_i) (2π / m)` is the total sphere area `4π R²`. -/
theorem spherical_cell_area_sum {n m : ℕ} (hm : m ≠ 0)
    (φ : Fin (n + 1) → ℝ) (h0 : φ 0 = -(Real.pi / 2))
    (hlast : φ (Fin.last n) = Real.pi / 2) {R : ℝ} :
    ∑ i : Fin n, ∑ j : Fin m,
        R ^ 2 * (Real.sin (φ i.succ) - Real.sin (φ i.castSucc)) * (2 * Real.pi / m)
      = 4 * Real.pi * R ^ 2 := by
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hinner : ∀ i : Fin n, (∑ j : Fin m,
      R ^ 2 * (Real.sin (φ i.succ) - Real.sin (φ i.castSucc)) * (2 * Real.pi / m))
      = (m : ℝ) * (R ^ 2 * (Real.sin (φ i.succ) - Real.sin (φ i.castSucc)) *
        (2 * Real.pi / m)) := by
    intro i
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hmassage : ∀ i : Fin n, R ^ 2 * (Real.sin (φ i.succ) - Real.sin (φ i.castSucc)) *
      (2 * Real.pi / m)
      = (R ^ 2 * (2 * Real.pi / m)) * (Real.sin (φ i.succ) - Real.sin (φ i.castSucc)) := by
    intro i
    ring
  have htele : ∑ i : Fin n, (Real.sin (φ i.succ) - Real.sin (φ i.castSucc)) = 2 := by
    have h : ∑ i : Fin n, (Real.sin (φ i.succ) - Real.sin (φ i.castSucc))
        = Real.sin (φ (Fin.last n)) - Real.sin (φ 0) :=
      telescope_sum_sub n (fun k => Real.sin (φ k))
    rw [hlast, h0, Real.sin_neg, Real.sin_pi_div_two] at h
    rw [h]
    norm_num
  simp only [hinner]
  rw [← Finset.mul_sum]
  simp only [hmassage]
  rw [← Finset.mul_sum, htele]
  field_simp
  ring

set_option linter.unusedVariables false in
/-- Spherical cell area weights integrate a constant `C` to `C` times the
total sphere area. -/
theorem spherical_cell_area_integrates_constant {n m : ℕ} (hm : m ≠ 0)
    (φ : Fin (n + 1) → ℝ) (h0 : φ 0 = -(Real.pi / 2))
    (hlast : φ (Fin.last n) = Real.pi / 2) {R C : ℝ} :
    ∑ i : Fin n, ∑ j : Fin m,
        (R ^ 2 * (Real.sin (φ i.succ) - Real.sin (φ i.castSucc)) * (2 * Real.pi / m)) * C
      = C * (4 * Real.pi * R ^ 2) := by
  have hbase : ∑ i : Fin n, ∑ j : Fin m,
      R ^ 2 * (Real.sin (φ i.succ) - Real.sin (φ i.castSucc)) * (2 * Real.pi / m)
      = 4 * Real.pi * R ^ 2 :=
    spherical_cell_area_sum hm φ h0 hlast
  calc ∑ i : Fin n, ∑ j : Fin m,
          (R ^ 2 * (Real.sin (φ i.succ) - Real.sin (φ i.castSucc)) * (2 * Real.pi / m)) * C
      = (∑ i : Fin n, ∑ j : Fin m,
          R ^ 2 * (Real.sin (φ i.succ) - Real.sin (φ i.castSucc)) * (2 * Real.pi / m)) * C := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_mul]
    _ = C * (4 * Real.pi * R ^ 2) := by rw [hbase]; ring

end EarthScience
