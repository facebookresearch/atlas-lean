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

A latitude partition `phi 0 < phi 1 < ... < phi n` of `[-pi/2, pi/2]` (`phi 0 = -pi/2`,
`phi n = pi/2`) and `m` longitude cells cut the sphere of radius `R` into cells; the cell in band
`i` and longitude cell `j` has area `R^2 (sin phi_{i+1} - sin phi_i) (2 pi / m)`. These areas are
nonnegative and sum to the sphere area `4 pi R^2`: summing over `i` telescopes to
`sin(pi/2) - sin(-pi/2) = 2`, and summing over the `m` longitude cells gives `2 pi`.

The telescoping identity itself uses only the endpoints. For an arbitrary endpoint sequence
(`phi 0 = -pi/2`, `phi n = pi/2`, no ordering) the summands are signed weights, not areas, and
can be negative, but they still sum to `4 pi R^2` and integrate a constant `C` to
`C * 4 pi R^2`; these are the signed-weight lemmas below. The ordering hypothesis
`StrictMono phi` makes the summands nonnegative cell areas.

## i. Overview

The inner sum over longitude cells is constant in `j`, giving a factor
`m`. The latitude sum telescopes. The constant-integration lemma
factors `C` out of the double sum and uses the sum lemma. For a
partition, every latitude lies in `[-pi/2, pi/2]`, where `sin` is
strictly increasing, so each band weight is nonnegative.

## ii. Key results

- `EarthScience.signed_band_weight_sum`: for any endpoint sequence, the
  signed weights sum to `4 pi R^2`.
- `EarthScience.signed_band_weight_sum_mul_const`: the signed weights
  integrate a constant `C` to `C * 4 pi R^2`.
- `EarthScience.spherical_cell_area_sum`: for a latitude partition, the
  cell areas are nonnegative and sum to `4 pi R^2`.

## iii. Table of contents

- A. Spherical cell area weights

## iv. References

- `Finset.sum_const`, `Finset.card_univ` in Mathlib.
- `Real.sin_pi_div_two`, `Real.sin_neg`,
  `Real.sin_lt_sin_of_lt_of_le_pi_div_two` in Mathlib.

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
/-- Signed band weights: for any endpoint sequence `φ` with `φ 0 = -π/2` and
`φ n = π/2` (no ordering is assumed, so a summand need not be an area and
can be negative) and `m ≠ 0` longitude cells, the weights
`R² (sin φ_{i+1} - sin φ_i) (2π / m)` sum to `4π R²`. See
`spherical_cell_area_sum` for latitude partitions. -/
lemma signed_band_weight_sum {n m : ℕ} (hm : m ≠ 0)
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
/-- The signed band weights of an endpoint sequence (as in
`signed_band_weight_sum`, no ordering assumed) integrate a constant `C`
to `C * 4π R²`. -/
lemma signed_band_weight_sum_mul_const {n m : ℕ} (hm : m ≠ 0)
    (φ : Fin (n + 1) → ℝ) (h0 : φ 0 = -(Real.pi / 2))
    (hlast : φ (Fin.last n) = Real.pi / 2) {R C : ℝ} :
    ∑ i : Fin n, ∑ j : Fin m,
        (R ^ 2 * (Real.sin (φ i.succ) - Real.sin (φ i.castSucc)) * (2 * Real.pi / m)) * C
      = C * (4 * Real.pi * R ^ 2) := by
  have hbase : ∑ i : Fin n, ∑ j : Fin m,
      R ^ 2 * (Real.sin (φ i.succ) - Real.sin (φ i.castSucc)) * (2 * Real.pi / m)
      = 4 * Real.pi * R ^ 2 :=
    signed_band_weight_sum hm φ h0 hlast
  calc ∑ i : Fin n, ∑ j : Fin m,
          (R ^ 2 * (Real.sin (φ i.succ) - Real.sin (φ i.castSucc)) * (2 * Real.pi / m)) * C
      = (∑ i : Fin n, ∑ j : Fin m,
          R ^ 2 * (Real.sin (φ i.succ) - Real.sin (φ i.castSucc)) * (2 * Real.pi / m)) * C := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_mul]
    _ = C * (4 * Real.pi * R ^ 2) := by rw [hbase]; ring

set_option linter.unusedVariables false in
/-- Spherical cell areas: for a latitude partition `φ` of `[-π/2, π/2]`
(strictly increasing, `φ 0 = -π/2`, `φ n = π/2`) and `m ≠ 0` longitude
cells, every cell area `R² (sin φ_{i+1} - sin φ_i) (2π / m)` is nonnegative
and the cell areas sum to the sphere area `4π R²`. -/
theorem spherical_cell_area_sum {n m : ℕ} (hm : m ≠ 0)
    (φ : Fin (n + 1) → ℝ) (hφ : StrictMono φ) (h0 : φ 0 = -(Real.pi / 2))
    (hlast : φ (Fin.last n) = Real.pi / 2) {R : ℝ} :
    (∀ i : Fin n,
        0 ≤ R ^ 2 * (Real.sin (φ i.succ) - Real.sin (φ i.castSucc)) * (2 * Real.pi / m)) ∧
      ∑ i : Fin n, ∑ j : Fin m,
          R ^ 2 * (Real.sin (φ i.succ) - Real.sin (φ i.castSucc)) * (2 * Real.pi / m)
        = 4 * Real.pi * R ^ 2 := by
  refine ⟨fun i => ?_, signed_band_weight_sum hm φ h0 hlast⟩
  have hlo : -(Real.pi / 2) ≤ φ i.castSucc := by
    rw [← h0]
    exact hφ.monotone (Fin.zero_le _)
  have hhi : φ i.succ ≤ Real.pi / 2 := by
    rw [← hlast]
    exact hφ.monotone (Fin.le_last _)
  have hsin : Real.sin (φ i.castSucc) < Real.sin (φ i.succ) :=
    Real.sin_lt_sin_of_lt_of_le_pi_div_two hlo hhi (hφ Fin.castSucc_lt_succ)
  have hm' : (0 : ℝ) ≤ 2 * Real.pi / m := div_nonneg (by positivity) (Nat.cast_nonneg m)
  exact mul_nonneg (mul_nonneg (sq_nonneg R) (sub_nonneg.2 hsin.le)) hm'

end EarthScience
