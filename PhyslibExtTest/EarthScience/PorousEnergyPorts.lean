/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.PorousEnergyPorts
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Radial Darcy profile and well-ledger checks

Concrete consumers of `PhyslibExt.EarthScience.PorousEnergyPorts`: on the annulus
`1 ≤ r ≤ exp 1` with head `0` at the well, signed injection and extraction move the head at
`r = exp 1` to `-1` and `1`, and with a negative transmissivity injection raises it to `1`.
On a chain of three cells of volume `2` with one injection, one production and a nonzero outlet,
one step takes the total mass from `30` to `29` and the total energy from `300` to `305`, as the
general ledger predicts, and no no-flux step reproduces it. A zero density is outside the
ledger's domain: its positivity premise is false, and the totalized enthalpy at `ρ = 0` would
drop the flow work.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Signed discharge and negative transmissivity
- B. Well and boundary sources in the energy ledger

## iv. References

- `PhyslibExt.EarthScience.PorousEnergyPorts`
-/

open EarthScience MathlibExt.Analysis.ODE.ContinuumBalances

/-! ## A. Signed discharge and negative transmissivity -/

/-- Signed injection and extraction on the annulus `1 ≤ r ≤ exp 1` with `Tr = 1` and head `0`
at the well: the injection `Q = 2 π` gives head `-1` at `r = exp 1`, and the extraction
`Q = -2 π` gives head `1`. -/
example :
    radialDarcyHead 0 (2 * Real.pi) 1 1 (Real.exp 1) = -1 ∧
      radialDarcyHead 0 (-(2 * Real.pi)) 1 1 (Real.exp 1) = 1 := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  constructor
  · unfold radialDarcyHead
    simp only [div_one, Real.log_exp, mul_one, zero_sub]
    field_simp
  · unfold radialDarcyHead
    simp only [div_one, Real.log_exp, mul_one, zero_sub]
    field_simp

/-- Negative-transmissivity fixture: with `Tr = -1`, head `0` at the well radius `1` and the
injection `Q = 2 π`, the profile rises to `1` at `r = exp 1`, toward the outward discharge. -/
example :
    radialDarcyHead 0 (2 * Real.pi) (-1) 1 (Real.exp 1) = 1 := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  unfold radialDarcyHead
  simp only [div_one, Real.log_exp, mul_one, zero_sub]
  field_simp

/-! ## B. Well and boundary sources in the energy ledger -/

/-- Fixture: three cells of volume `Δx = 2` with mass densities `5` and energy densities `50`,
face mass fluxes `(1, 3, 2, 4)` (inflow `1` at the left face, outlet `4` at the right face), one
injection of `3` into cell `0` at specific enthalpy `20` and one production of `2` from cell `2`
at that cell's specific enthalpy `8 + 2 / 1 = 10`; every face carries specific enthalpy `10`.
One step `dt = 1/2` takes the total mass from `30` to `29 = 30 + dt ((1 - 4) + (3 - 2))` and the
total energy from `300` to `305 = 300 + dt ((10 - 40) + (60 - 20))`. -/
example :
    (2 : ℝ) * ∑ i : Fin 3, (![5, 5, 5] i + 1 / 2 *
        wellCellRate ⟨2, two_pos⟩ ![1, 3, 2, 4] (fun i => ![3, 0, 0] i - ![0, 0, 2] i) i) = 29 ∧
      (2 : ℝ) * ∑ i : Fin 3, (![50, 50, 50] i + 1 / 2 *
        wellCellRate ⟨2, two_pos⟩
          (faceEnthalpyFlux ![1, 3, 2, 4] (fun _ => 8) (fun _ => 2) (fun _ => 1) (fun _ => one_pos))
          (wellEnergyRate ![3, 0, 0] ![0, 0, 2] ![20, 0, 0] (fun _ => 8) (fun _ => 2)
            (fun _ => 1) (fun _ => one_pos)) i) = 305 := by
  refine ⟨?_, ?_⟩
  · norm_num [Fin.sum_univ_three, wellCellRate, discreteBalance,
      show ((⟨2, two_pos⟩ : {x : ℝ // 0 < x}) : ℝ) = 2 from rfl]
  · norm_num [Fin.sum_univ_three, wellCellRate, discreteBalance, faceEnthalpyFlux,
      wellEnergyRate, ControlVolumes.specificEnthalpy,
      show ((⟨2, two_pos⟩ : {x : ℝ // 0 < x}) : ℝ) = 2 from rfl]

/-- The no-flux specialization cannot represent this open chain: for every flux field with zero
exterior fluxes, the no-flux step without wells keeps the fixture's total mass at `30`
(`sum_add_mul_discreteBalance_of_noFlux`), so it differs from the fixture step with one
injection, one production and a nonzero outlet, which ends at `29`. -/
example (F : Fin 4 → ℝ) (h0 : F 0 = 0)
    (h3 : F (Fin.last 3) = 0) :
    (2 : ℝ) * ∑ i : Fin 3, (![5, 5, 5] i + 1 / 2 * discreteBalance ⟨2, two_pos⟩ F i) ≠
      2 * ∑ i : Fin 3, (![5, 5, 5] i + 1 / 2 *
        wellCellRate ⟨2, two_pos⟩ ![1, 3, 2, 4] (fun i => ![3, 0, 0] i - ![0, 0, 2] i) i) := by
  have hL : (2 : ℝ) * ∑ i : Fin 3, (![5, 5, 5] i + 1 / 2 * discreteBalance ⟨2, two_pos⟩ F i)
      = 30 := by
    have h := sum_add_mul_discreteBalance_of_noFlux (⟨2, two_pos⟩ : {x : ℝ // 0 < x})
      (1 / 2 : ℝ) ![5, 5, 5] h0 h3
    rw [h]
    norm_num [Fin.sum_univ_three]
  have hR : (2 : ℝ) * ∑ i : Fin 3, (![5, 5, 5] i + 1 / 2 *
      wellCellRate ⟨2, two_pos⟩ ![1, 3, 2, 4] (fun i => ![3, 0, 0] i - ![0, 0, 2] i) i) = 29 := by
    norm_num [Fin.sum_univ_three, wellCellRate, discreteBalance,
      show ((⟨2, two_pos⟩ : {x : ℝ // 0 < x}) : ℝ) = 2 from rfl]
  rw [hL, hR]
  norm_num

/-- The fixture's cell rates through the generic ledger: they sum to the transport total
`totalDiscreteChange = -(4 - 1) / 2` plus the well total `(3 - 2) / 2`, that is `-1`. -/
example :
    ∑ i : Fin 3, wellCellRate ⟨2, two_pos⟩ ![1, 3, 2, 4] (fun i => ![3, 0, 0] i - ![0, 0, 2] i) i =
      -1 := by
  have hlast : (![1, 3, 2, 4] : Fin 4 → ℝ) (Fin.last 3) = 4 := rfl
  rw [(stock_add_mul_wellCellRate ⟨2, two_pos⟩ 0 ![0, 0, 0] ![1, 3, 2, 4]
    (fun i => ![3, 0, 0] i - ![0, 0, 2] i)).1, totalDiscreteChange_eq]
  norm_num [Fin.sum_univ_three, hlast,
    show ((⟨2, two_pos⟩ : {x : ℝ // 0 < x}) : ℝ) = 2 from rfl]

/-- The fixture's step through the mass and energy ledger: the total mass changes by
`dt ((Fm 0 - Fm 3) + ∑ (qI - qP)) = (1/2) ((1 - 4) + (3 - 2)) = -1`, from `30` to `29`, and the
total energy by `dt` times the boundary enthalpy inflow `10 - 40` plus the well energy total
`60 - 20`, from `300` to `305`. -/
example :
    ((⟨2, two_pos⟩ : {x : ℝ // 0 < x}) : ℝ) * ∑ i : Fin 3, (![5, 5, 5] i + 1 / 2 *
        wellCellRate ⟨2, two_pos⟩ ![1, 3, 2, 4] (fun i => ![3, 0, 0] i - ![0, 0, 2] i) i) = 29 ∧
      ((⟨2, two_pos⟩ : {x : ℝ // 0 < x}) : ℝ) * ∑ i : Fin 3, (![50, 50, 50] i + 1 / 2 *
        wellCellRate ⟨2, two_pos⟩
          (faceEnthalpyFlux ![1, 3, 2, 4] (fun _ => 8) (fun _ => 2) (fun _ => 1) (fun _ => one_pos))
          (wellEnergyRate ![3, 0, 0] ![0, 0, 2] ![20, 0, 0] (fun _ => 8) (fun _ => 2)
            (fun _ => 1) (fun _ => one_pos)) i) = 305 := by
  obtain ⟨hm, he⟩ := well_boundary_ledger ⟨2, two_pos⟩ (1 / 2) ![5, 5, 5] ![50, 50, 50]
    ![1, 3, 2, 4] (fun _ => 8) (fun _ => 2) (fun _ => 1) ![3, 0, 0] ![0, 0, 2] ![20, 0, 0]
    (fun _ => 8) (fun _ => 2) (fun _ => 1) (fun _ => one_pos) (fun _ => one_pos)
  have hlast : (![1, 3, 2, 4] : Fin 4 → ℝ) (Fin.last 3) = 4 := rfl
  rw [hm, he]
  norm_num [Fin.sum_univ_three, faceEnthalpyFlux, wellEnergyRate, hlast,
    ControlVolumes.specificEnthalpy, show ((⟨2, two_pos⟩ : {x : ℝ // 0 < x}) : ℝ) = 2 from rfl]

/-- A zero face density is outside the ledger's domain: the positivity premise that
`faceEnthalpyFlux` takes is false for the densities `(1, 0)`. -/
example : ¬ ∀ j : Fin 2, (0 : ℝ) < ![1, 0] j := fun h => by
  simpa using h 1

/-- What the domain restriction excludes: Lean's `x / 0 = 0` turns the enthalpy
`specificEnthalpy e p 0` into `e`, dropping the flow work, so at `e = 8` and `p = 2` a unit mass
flux would carry `8` at `ρ = 0` instead of the `10` it carries at `ρ = 1`. -/
example :
    ControlVolumes.specificEnthalpy 8 2 0 = 8 ∧ ControlVolumes.specificEnthalpy 8 2 1 = 10 := by
  norm_num [ControlVolumes.specificEnthalpy]
