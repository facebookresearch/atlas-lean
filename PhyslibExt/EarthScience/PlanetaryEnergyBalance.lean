/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Planetary energy balance

## i. Overview

For `sigma > 0`, `S >= 0`, `alpha ∈ [0,1]`, the equilibrium
`sigma * T^4 = (1 - alpha) * S / 4` has a unique `T >= 0`. The factor
`1/4` is the geometric sphere/disk area ratio for the specified one-box
outgoing law. `T` is an effective temperature in Kelvin, not an observed
surface temperature.

## ii. Key results

- `EarthScience.planetaryEnergyBalance_equilibrium_exists`: a nonnegative
  equilibrium exists.
- `EarthScience.planetaryEnergyBalance_equilibrium_unique`: the nonnegative
  equilibrium is unique.
- `EarthScience.planetaryEnergyBalance_full_albedo`: `alpha = 1` gives `T = 0`.
- `EarthScience.planetaryEnergyBalance_witness`: `sigma = 1, S = 4, alpha = 0`
  gives `T = 1`.

## iii. Table of contents

- A. Main results

## iv. References

- D. L. Hartmann, *Global Physical Climatology*, 2nd ed., Elsevier (2016),
  Chapter 2 (The Global Energy Balance), emission temperature of a planet:
  equating absorbed solar radiation `(1 - alpha) * S / 4` with blackbody
  emission `sigma * T^4` defines the emission temperature, where the factor
  `4` is the ratio of the surface area of a sphere to its shadow area (a
  disk of the same radius), and this temperature need not be the surface
  temperature.
-/

@[expose] public section

namespace EarthScience


set_option linter.unusedVariables false in
/-- Planetary energy balance: an equilibrium `T >= 0` with
`sigma * T^4 = (1 - alpha) * S / 4` exists. -/
theorem planetaryEnergyBalance_equilibrium_exists {σ S α : ℝ} (hσ : 0 < σ) (hS : 0 ≤ S)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ T : ℝ, 0 ≤ T ∧ σ * T ^ 4 = (1 - α) * S / 4 := by
  have hσne : σ ≠ 0 := ne_of_gt hσ
  have h1α : 0 ≤ 1 - α := sub_nonneg.mpr hα1
  have hnum : 0 ≤ (1 - α) * S / 4 := div_nonneg (mul_nonneg h1α hS) (by norm_num)
  have hr : 0 ≤ (1 - α) * S / 4 / σ := div_nonneg hnum (le_of_lt hσ)
  refine ⟨Real.sqrt (Real.sqrt ((1 - α) * S / 4 / σ)), Real.sqrt_nonneg _, ?_⟩
  have hsq1 : Real.sqrt ((1 - α) * S / 4 / σ) ^ 2 = (1 - α) * S / 4 / σ :=
    Real.sq_sqrt hr
  have hsq2 : Real.sqrt (Real.sqrt ((1 - α) * S / 4 / σ)) ^ 2
      = Real.sqrt ((1 - α) * S / 4 / σ) :=
    Real.sq_sqrt (Real.sqrt_nonneg _)
  have hT4 : Real.sqrt (Real.sqrt ((1 - α) * S / 4 / σ)) ^ 4
      = (1 - α) * S / 4 / σ := by
    calc Real.sqrt (Real.sqrt ((1 - α) * S / 4 / σ)) ^ 4
        = (Real.sqrt (Real.sqrt ((1 - α) * S / 4 / σ)) ^ 2) ^ 2 := by ring
      _ = Real.sqrt ((1 - α) * S / 4 / σ) ^ 2 := by rw [hsq2]
      _ = (1 - α) * S / 4 / σ := hsq1
  rw [hT4]
  field_simp

/-- Planetary energy balance: the nonnegative equilibrium is unique. -/
theorem planetaryEnergyBalance_equilibrium_unique {σ S α T₁ T₂ : ℝ} (hσ : 0 < σ)
    (hT₁ : 0 ≤ T₁) (hT₂ : 0 ≤ T₂)
    (h₁ : σ * T₁ ^ 4 = (1 - α) * S / 4) (h₂ : σ * T₂ ^ 4 = (1 - α) * S / 4) :
    T₁ = T₂ := by
  have hσne : σ ≠ 0 := ne_of_gt hσ
  have hpow : T₁ ^ 4 = T₂ ^ 4 := by
    have h : σ * T₁ ^ 4 = σ * T₂ ^ 4 := by rw [h₁, h₂]
    exact mul_left_cancel₀ hσne h
  have hsq : (T₁ ^ 2) ^ 2 = (T₂ ^ 2) ^ 2 := by
    have e1 : T₁ ^ 4 = (T₁ ^ 2) ^ 2 := by ring
    have e2 : T₂ ^ 4 = (T₂ ^ 2) ^ 2 := by ring
    rw [e1, e2] at hpow
    exact hpow
  have habs2 : |T₁ ^ 2| = |T₂ ^ 2| := (sq_eq_sq_iff_abs_eq_abs _ _).mp hsq
  have h2 : T₁ ^ 2 = T₂ ^ 2 := by
    have n1 : 0 ≤ T₁ ^ 2 := sq_nonneg _
    have n2 : 0 ≤ T₂ ^ 2 := sq_nonneg _
    rw [abs_of_nonneg n1, abs_of_nonneg n2] at habs2
    exact habs2
  have habs : |T₁| = |T₂| := (sq_eq_sq_iff_abs_eq_abs _ _).mp h2
  rw [abs_of_nonneg hT₁, abs_of_nonneg hT₂] at habs
  exact habs

set_option linter.unusedVariables false in
/-- Boundary case `alpha = 1` (zero absorption): the equilibrium is `T = 0`. -/
theorem planetaryEnergyBalance_full_albedo {σ S : ℝ} (hσ : 0 < σ) (hS : 0 ≤ S) {T : ℝ} (hT : 0 ≤ T)
    (h : σ * T ^ 4 = (1 - (1 : ℝ)) * S / 4) :
    T = 0 := by
  have hσne : σ ≠ 0 := ne_of_gt hσ
  have h0 : σ * T ^ 4 = 0 := by
    have hrhs : (1 - (1 : ℝ)) * S / 4 = 0 := by ring
    rw [hrhs] at h
    exact h
  have h4 : T ^ 4 = 0 := by
    rcases (mul_eq_zero.mp h0) with hσ0 | hT0
    · exact (hσne hσ0).elim
    · exact hT0
  exact (pow_eq_zero_iff (show 4 ≠ 0 by norm_num)).mp h4

/-- Non-vacuous witness: `sigma = 1, S = 4, alpha = 0` gives `T = 1`. -/
theorem planetaryEnergyBalance_witness :
    ∃ T : ℝ, 0 ≤ T ∧ (1 : ℝ) * T ^ 4 = (1 - (0 : ℝ)) * 4 / 4 ∧ T = 1 := by
  exact ⟨1, by norm_num, by norm_num, rfl⟩


end EarthScience
