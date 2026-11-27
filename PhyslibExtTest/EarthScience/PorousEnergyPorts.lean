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
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Radial Darcy profile, well-ledger and fractional-flow checks

Concrete consumers of `PhyslibExt.EarthScience.PorousEnergyPorts`: on the annulus
`1 ≤ r ≤ exp 1` with head `0` at the well, signed injection and extraction move the head at
`r = exp 1` to `-1` and `1`, and with a negative transmissivity injection raises it to `1`.
On a chain of three cells of volume `2` with one injection, one production and a nonzero outlet,
one step takes the total mass from `30` to `29` and the total energy from `300` to `315`, as the
general ledger predicts, and no no-flux step reproduces it. The cells store the fluid state
`ρ = 20`, `e = 10` at porosity `1/4` (mass `5`, energy `50` per unit volume), so the producing
cell's enthalpy `12` follows from its stored mass and energy. A zero density is outside the
ledger's domain: its positivity premise is false, and the totalized enthalpy at `ρ = 0` would
drop the flow work. Water at the end point of the mobile range floods three cells
(`μo = 2`, `μw = 1`, `ΔS = 2 / 5`, `ν B = 9 / 10`): the step keeps every saturation in range,
matches the normalized upwind step, and raises the water volume by the inflow minus the outflow.
Dropping `ΔS` from the CFL number admits a step that leaves the range, and the saturation sum of
the open chain is not conserved.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Signed discharge and negative transmissivity
- B. Well and boundary sources in the energy ledger
- C. Fractional flow and the upwind step

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

/-- Fixture: three cells of volume `Δx = 2`, each storing the fluid state `ρ = 20`, `e = 10`,
`p = 40` at porosity `1/4`, that is the mass `5` and the energy `50` per unit volume; face mass
fluxes `(1, 3, 2, 4)` (inflow `1` at the left face, outlet `4` at the right face) carrying the
same state, of specific enthalpy `10 + 40 / 20 = 12`; one injection of `3` into cell `0` at
specific enthalpy `30` and one production of `2` from cell `2` at that cell's specific enthalpy
`12 = (50 + 40 / 4) / 5`. One step `dt = 1/2` takes the total mass from `30` to
`29 = 30 + dt ((1 - 4) + (3 - 2))` and the total energy from `300` to
`315 = 300 + dt ((12 - 48) + (90 - 24))`. -/
example :
    (2 : ℝ) * ∑ i : Fin 3, (![5, 5, 5] i + 1 / 2 *
        wellCellRate ⟨2, two_pos⟩ ![1, 3, 2, 4] (fun i => ![3, 0, 0] i - ![0, 0, 2] i) i) = 29 ∧
      (2 : ℝ) * ∑ i : Fin 3, (![50, 50, 50] i + 1 / 2 *
        wellCellRate ⟨2, two_pos⟩
          (faceEnthalpyFlux ![1, 3, 2, 4] (fun _ => 10) (fun _ => 40) (fun _ => 20)
            (fun _ => by norm_num))
          (wellEnergyRate ![3, 0, 0] ![0, 0, 2] ![30, 0, 0] (fun _ => 10) (fun _ => 40)
            (fun _ => 20) (fun _ => by norm_num)) i) = 315 := by
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

/-- The fixture's step through the mass and energy ledger. The stored state is consistent:
`5 = (1/4) * 20` and `50 = 5 * 10`. The total mass changes by
`dt ((Fm 0 - Fm 3) + ∑ (qI - qP)) = (1/2) ((1 - 4) + (3 - 2)) = -1`, from `30` to `29`, and the
total energy by `dt` times the boundary enthalpy inflow `12 - 48` plus the well total
`3 * 30 - 2 * (50 + (1/4) * 40) / 5 = 66`, from `300` to `315`. -/
example :
    ((⟨2, two_pos⟩ : {x : ℝ // 0 < x}) : ℝ) * ∑ i : Fin 3, (![5, 5, 5] i + 1 / 2 *
        wellCellRate ⟨2, two_pos⟩ ![1, 3, 2, 4] (fun i => ![3, 0, 0] i - ![0, 0, 2] i) i) = 29 ∧
      ((⟨2, two_pos⟩ : {x : ℝ // 0 < x}) : ℝ) * ∑ i : Fin 3, (![50, 50, 50] i + 1 / 2 *
        wellCellRate ⟨2, two_pos⟩
          (faceEnthalpyFlux ![1, 3, 2, 4] (fun _ => 10) (fun _ => 40) (fun _ => 20)
            (fun _ => by norm_num))
          (wellEnergyRate ![3, 0, 0] ![0, 0, 2] ![30, 0, 0] (fun _ => 10) (fun _ => 40)
            (fun _ => 20) (fun _ => by norm_num)) i) = 315 := by
  obtain ⟨hm, he⟩ := well_boundary_ledger ⟨2, two_pos⟩ (1 / 2) ![5, 5, 5] ![50, 50, 50]
    ![1, 3, 2, 4] (fun _ => 10) (fun _ => 40) (fun _ => 20) ![3, 0, 0] ![0, 0, 2] ![30, 0, 0]
    (fun _ => 10) (fun _ => 40) (fun _ => 20) (fun _ => 1 / 4) (fun _ => by norm_num)
    (fun _ => by norm_num) (fun _ => by norm_num) (fun i => by fin_cases i <;> norm_num)
    (fun i => by fin_cases i <;> norm_num)
  have hlast : (![1, 3, 2, 4] : Fin 4 → ℝ) (Fin.last 3) = 4 := rfl
  rw [hm, he]
  norm_num [Fin.sum_univ_three, faceEnthalpyFlux, hlast, ControlVolumes.specificEnthalpy,
    show ((⟨2, two_pos⟩ : {x : ℝ // 0 < x}) : ℝ) = 2 from rfl]

/-- The producing cell's enthalpy from its stored state: with mass `5`, energy `50`, porosity
`1/4` and pressure `40`, the produced enthalpy is `(50 + 10) / 5 = 12`, so the well energy rate
of cell `2` is `-2 * 12 = -24`. -/
example :
    wellEnergyRate ![3, 0, 0] ![0, 0, 2] ![30, 0, 0] (fun _ => 10) (fun _ => 40) (fun _ => 20)
      (fun _ => by norm_num) 2 = -24 := by
  rw [wellEnergyRate_eq_stored (m := ![5, 5, 5]) (E := ![50, 50, 50]) (φ := fun _ => 1 / 4)
    (fun _ => by norm_num) (fun _ => by norm_num) (fun i => by fin_cases i <;> norm_num)
    (fun i => by fin_cases i <;> norm_num)]
  norm_num

/-- Storage consistency rejects a cell state that does not match the stored mass and energy:
the state `ρ = 1`, `e = 8` with the stored mass `5` and energy `50` would need `50 = 5 * 8`,
for every porosity. -/
example : ¬ ∃ φ : ℝ, 0 < φ ∧ (5 : ℝ) = φ * 1 ∧ (50 : ℝ) = 5 * 8 := by
  rintro ⟨φ, -, -, h⟩
  norm_num at h

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

/-! ## C. Fractional flow and the upwind step -/

/-- Fixture: oil `μo = 2`, water `μw = 1` (`B = 9 / 4`), `Swc = Sor = 3 / 10` (`ΔS = 2 / 5`),
pore volume `1 / 4` per cell, `Q dt = 1 / 25`, so `ν = 2 / 5` and `ν B = 9 / 10`. Water at the
end point `Sin = 1 - Sor = 7 / 10` (`f = 1`) flows into the cells `S = (7 / 10, 1 / 2, 2 / 5)`
(normalized `(1, 1 / 2, 1 / 4)`, outlet `f = 2 / 11`). The step gives
`(7 / 10, 83 / 150, 394 / 825)`, and the water volume rises from `2 / 5` to
`119 / 275 = 2 / 5 + (1 / 25) (1 - 2 / 11)`. -/
example :
    cflNumber (1 / 25) 1 (1 / 4) 1 1 (1 - 3 / 10 - 3 / 10) = 2 / 5 ∧
      cflNumber (1 / 25) 1 (1 / 4) 1 1 (1 - 3 / 10 - 3 / 10) * fracFlowBound 2 1 = 9 / 10 ∧
      fracFlow 2 1 (normSat (3 / 10) (3 / 10) (7 / 10)) = 1 ∧
      fracFlow 2 1 (normSat (3 / 10) (3 / 10) (2 / 5)) = 2 / 11 ∧
      satStep 2 1 (3 / 10) (3 / 10) (1 / 25) 1 (1 / 4) 1 1 (7 / 10) ![7 / 10, 1 / 2, 2 / 5] 0 =
        7 / 10 ∧
      satStep 2 1 (3 / 10) (3 / 10) (1 / 25) 1 (1 / 4) 1 1 (7 / 10) ![7 / 10, 1 / 2, 2 / 5] 1 =
        83 / 150 ∧
      satStep 2 1 (3 / 10) (3 / 10) (1 / 25) 1 (1 / 4) 1 1 (7 / 10) ![7 / 10, 1 / 2, 2 / 5] 2 =
        394 / 825 ∧
      1 / 4 * 1 * 1 * ∑ i, satStep 2 1 (3 / 10) (3 / 10) (1 / 25) 1 (1 / 4) 1 1 (7 / 10)
        ![7 / 10, 1 / 2, 2 / 5] i = 119 / 275 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [cflNumber]
  · norm_num [cflNumber, fracFlowBound]
  · norm_num [fracFlow, normSat]
  · norm_num [fracFlow, normSat]
  · norm_num [satStep, fracFlow, normSat, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_succ]
  · norm_num [satStep, fracFlow, normSat, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_succ]
  · norm_num [satStep, fracFlow, normSat, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_succ]
  · rw [Fin.sum_univ_three]
    norm_num [satStep, fracFlow, normSat, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_succ]

/-- The flood step through the interval theorem: with `ν B = 9 / 10 ≤ 1`, every cell of the step
stays in `[Swc, 1 - Sor] = [3 / 10, 7 / 10]`. -/
example (i : Fin 3) :
    satStep 2 1 (3 / 10) (3 / 10) (1 / 25) 1 (1 / 4) 1 1 (7 / 10) ![7 / 10, 1 / 2, 2 / 5] i ∈
      Set.Icc (3 / 10) (1 - 3 / 10) :=
  satStep_mem_Icc (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [cflNumber, fracFlowBound]) (by norm_num)
    (fun j => by fin_cases j <;> norm_num) i

/-- The physical flood step is the normalized upwind step with `ν = 2 / 5`: behind the end-point
inflow, the normalized cell `1` moves from `1 / 2` to `1 / 2 - (2 / 5) (2 / 3 - 1) = 19 / 30`. -/
example :
    normSat (3 / 10) (3 / 10)
        (satStep 2 1 (3 / 10) (3 / 10) (1 / 25) 1 (1 / 4) 1 1 (7 / 10) ![7 / 10, 1 / 2, 2 / 5] 1) =
      19 / 30 := by
  rw [normSat_satStep]
  norm_num [upwindStep, upwindUpdate, cflNumber, fracFlow, normSat]

/-- The flood's water volume through the balance theorem: it changes by the inflow
`Q dt f (s_in) = 1 / 25` minus the outflow `Q dt f (s_out) = (1 / 25) (2 / 11)`, from `2 / 5` to
`119 / 275`. -/
example :
    1 / 4 * 1 * 1 * ∑ i, satStep 2 1 (3 / 10) (3 / 10) (1 / 25) 1 (1 / 4) 1 1 (7 / 10)
      ![7 / 10, 1 / 2, 2 / 5] i = 119 / 275 := by
  rw [satStep_volume_balance _ (by norm_num)]
  norm_num [fracFlow, normSat, Fin.sum_univ_succ, Fin.last]

/-- The Lipschitz bound on two of the flood's normalized saturations:
`f (1 / 2) - f (1 / 4) = 2 / 3 - 2 / 11 = 16 / 33` lies in
`[0, B (1 / 2 - 1 / 4)] = [0, 9 / 16]`. -/
example :
    fracFlow 2 1 (1 / 2) - fracFlow 2 1 (1 / 4) ∈
      Set.Icc 0 (fracFlowBound 2 1 * (1 / 2 - 1 / 4)) :=
  fracFlow_sub_mem_Icc (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Omitting `ΔS` in the CFL rescaling is wrong. With the fixture's viscosities and saturation
range, pore volume `1 / 4` and `Q dt = 1 / 9`, the number `Q dt / (φ A dx) = 4 / 9` without `ΔS`
passes `· * B ≤ 1`, but the CFL number with `ΔS` is `10 / 9` (`ν B = 5 / 2 > 1`), and one step
of the admissible cell `S = 2 / 5` with inflow `7 / 10` gives `42 / 55 > 1 - Sor`. -/
example :
    (2 / 5 : ℝ) ∈ Set.Icc (3 / 10) (1 - 3 / 10) ∧ (7 / 10 : ℝ) ∈ Set.Icc (3 / 10) (1 - 3 / 10) ∧
      1 / 9 * 1 / (1 / 4 * 1 * 1) * fracFlowBound 2 1 ≤ 1 ∧
      1 < cflNumber (1 / 9) 1 (1 / 4) 1 1 (1 - 3 / 10 - 3 / 10) * fracFlowBound 2 1 ∧
      1 - 3 / 10 < satStep 2 1 (3 / 10) (3 / 10) (1 / 9) 1 (1 / 4) 1 1 (7 / 10) ![2 / 5] 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · norm_num [fracFlowBound]
  · norm_num [cflNumber, fracFlowBound]
  · norm_num [satStep, fracFlow, normSat, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_succ, Matrix.cons_val_fin_one]

/-- A periodic conservation identity is wrong for the open chain: in the fixture the sum of the
saturations changes (`8 / 5` before, `476 / 275` after), because the inlet and outlet terms do not
cancel. -/
example :
    ∑ i, satStep 2 1 (3 / 10) (3 / 10) (1 / 25) 1 (1 / 4) 1 1 (7 / 10) ![7 / 10, 1 / 2, 2 / 5] i ≠
      ∑ i, ![(7 / 10 : ℝ), 1 / 2, 2 / 5] i := by
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  norm_num [satStep, fracFlow, normSat, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_succ]
