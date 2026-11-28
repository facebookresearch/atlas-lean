/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.ShallowWaterLakeAtRestUpdate
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Shallow-water lake-at-rest update checks

Concrete consumers of
`PhyslibExt.EarthScience.ShallowWaterLakeAtRestUpdate`: the public
shapes, chain wiring, the three unequal-bed cells `z = (0, 2, 1)` at
`η = 3`, one cell between walls, the nonzero-discharge control and the
dry-endpoint exclusion.

## i. Overview

The left-state physical flux below is a private fixture. It is
consistent on wet states and makes the face and update values concrete.

## ii. Key results

No new public definitions or results are introduced here.

## iii. Table of contents

- A. Public shapes and wiring
- B. Three unequal bed cells
- C. Boundary and negative controls

## iv. References

- `PhyslibExt.EarthScience.ShallowWaterLakeAtRestUpdate`
-/

open EarthScience.HydrostaticReconstruction
open MathlibExt.Analysis.ODE.ContinuumBalances (discreteBalance)

/-- The left-state physical flux, used only as a test fixture. -/
private noncomputable def leftStateFlux (g : ℝ) : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ :=
  fun a _ => (a.2, a.2 * a.2 / a.1 + g * a.1 ^ 2 / 2)

/-- Wet-state consistency of the left-state fixture flux. -/
private lemma leftStateFlux_consistent (g : ℝ) :
    ∀ h u : ℝ, 0 < h →
      leftStateFlux g (h, h * u) (h, h * u) =
        (h * u, h * u ^ 2 + g * h ^ 2 / 2) := by
  intro h u hh
  have hne : h ≠ 0 := ne_of_gt hh
  have hdiv : (h * u) * (h * u) / h = h * u ^ 2 := by
    rw [div_eq_iff hne]
    ring
  show (h * u, (h * u) * (h * u) / h + g * h ^ 2 / 2) = _
  rw [hdiv]

/-! ## A. Public shapes and wiring -/

/-- Public shape of the full corrected-flux identity. -/
example {g η hL uL hR uR zL zR : ℝ}
    (numFlux : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ)
    (hcons : ∀ h u : ℝ, 0 < h →
      numFlux (h, h * u) (h, h * u) = (h * u, h * u ^ 2 + g * h ^ 2 / 2))
    (hηL : hL + zL = η) (hηR : hR + zR = η) (hwet : max zL zR < η)
    (hqL : hL * uL = 0) (hqR : hR * uR = 0) :
    leftFlux g numFlux hL uL hR uR zL zR = (0, g * hL ^ 2 / 2) ∧
      rightFlux g numFlux hL uL hR uR zL zR = (0, g * hR ^ 2 / 2) :=
  corrected_fluxes_eq_of_lake_at_rest numFlux hcons hηL hηR hwet hqL hqR

/-- Public shape of the wall-flux identity. -/
example {g h u z : ℝ} (numFlux : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ)
    (hcons : ∀ h u : ℝ, 0 < h →
      numFlux (h, h * u) (h, h * u) = (h * u, h * u ^ 2 + g * h ^ 2 / 2))
    (hh : 0 < h) (hq : h * u = 0) :
    leftWallFlux g numFlux h u z = (0, g * h ^ 2 / 2) ∧
      rightWallFlux g numFlux h u z = (0, g * h ^ 2 / 2) :=
  wall_fluxes_eq_of_rest numFlux hcons hh hq

/-- Public shape of the main update invariance. -/
example {n : ℕ} {g η Δt : ℝ}
    (Δx : Fin (n + 1) → {x : ℝ // 0 < x})
    (numFlux : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ)
    (hcons : ∀ h u : ℝ, 0 < h →
      numFlux (h, h * u) (h, h * u) = (h * u, h * u ^ 2 + g * h ^ 2 / 2))
    {h u z : Fin (n + 1) → ℝ}
    (hη : ∀ i, h i + z i = η) (hwet : ∀ i, z i < η)
    (hq : ∀ i, h i * u i = 0) (i : Fin (n + 1)) :
    cellUpdate g Δt Δx numFlux h u z i = (h i, h i * u i) :=
  cellUpdate_eq_of_lake_at_rest Δx numFlux hcons hη hwet hq i

/-- Public shape of the discrete-balance mass bridge. -/
example {n : ℕ} (g Δt : ℝ) (Δx : {x : ℝ // 0 < x})
    (numFlux : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ) (h u z : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) :
    (cellUpdate g Δt (fun _ => Δx) numFlux h u z i).1 =
      h i + Δt * discreteBalance Δx (faceMassFlux g numFlux h u z) i :=
  cellUpdate_fst_eq_discreteBalance g Δt Δx numFlux h u z i

/-- Public shape of the nonzero-discharge control. -/
example {g η Δt u : ℝ} (Δx : Fin 3 → {x : ℝ // 0 < x})
    (numFlux : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ)
    (hcons : ∀ h u : ℝ, 0 < h →
      numFlux (h, h * u) (h, h * u) = (h * u, h * u ^ 2 + g * h ^ 2 / 2))
    {z : Fin 3 → ℝ} (h01 : z 0 < z 1) (h12 : z 1 < z 2) (hwet : z 2 < η)
    (hu : u ≠ 0) (hΔt : Δt ≠ 0) :
    (cellUpdate g Δt Δx numFlux (fun i => η - z i) (fun _ => u) z 1).1 ≠
      η - z 1 :=
  cellUpdate_fst_ne_of_uniform_flow Δx numFlux hcons h01 h12 hwet hu hΔt

/-- Public shape of the dry-endpoint exclusion. -/
example (g Δt : ℝ) (hΔt : Δt ≠ 0) (Δx : Fin 2 → {x : ℝ // 0 < x})
    {z : Fin 2 → ℝ} (h01 : z 0 < z 1) :
    ∃ numFlux : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ,
      (∀ h u : ℝ, 0 < h →
        numFlux (h, h * u) (h, h * u) = (h * u, h * u ^ 2 + g * h ^ 2 / 2)) ∧
      cellUpdate g Δt Δx numFlux (fun i => z 1 - z i) (fun _ => 0) z 0 ≠
        (z 1 - z 0, 0) :=
  exists_cellUpdate_ne_of_dry g Δt hΔt Δx h01

/-- Three-cell wiring: the flux each cell sees at its left face. -/
private lemma leftFaceFlux_three_zero (g : ℝ)
    (nf : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ) (h u z : Fin 3 → ℝ) :
    leftFaceFlux g nf h u z 0 = leftWallFlux g nf (h 0) (u 0) (z 0) := rfl

private lemma leftFaceFlux_three_one (g : ℝ)
    (nf : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ) (h u z : Fin 3 → ℝ) :
    leftFaceFlux g nf h u z 1 =
      rightFlux g nf (h 0) (u 0) (h 1) (u 1) (z 0) (z 1) := rfl

private lemma leftFaceFlux_three_two (g : ℝ)
    (nf : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ) (h u z : Fin 3 → ℝ) :
    leftFaceFlux g nf h u z 2 =
      rightFlux g nf (h 1) (u 1) (h 2) (u 2) (z 1) (z 2) := rfl

/-- Three-cell wiring: the flux each cell sees at its right face. -/
private lemma rightFaceFlux_three_zero (g : ℝ)
    (nf : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ) (h u z : Fin 3 → ℝ) :
    rightFaceFlux g nf h u z 0 =
      leftFlux g nf (h 0) (u 0) (h 1) (u 1) (z 0) (z 1) := rfl

private lemma rightFaceFlux_three_one (g : ℝ)
    (nf : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ) (h u z : Fin 3 → ℝ) :
    rightFaceFlux g nf h u z 1 =
      leftFlux g nf (h 1) (u 1) (h 2) (u 2) (z 1) (z 2) := rfl

private lemma rightFaceFlux_three_two (g : ℝ)
    (nf : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ) (h u z : Fin 3 → ℝ) :
    rightFaceFlux g nf h u z 2 = rightWallFlux g nf (h 2) (u 2) (z 2) := rfl

private lemma leftFaceFlux_one_zero (g : ℝ)
    (nf : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ) (h u z : Fin 1 → ℝ) :
    leftFaceFlux g nf h u z 0 = leftWallFlux g nf (h 0) (u 0) (z 0) := rfl

private lemma rightFaceFlux_one_zero (g : ℝ)
    (nf : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ) (h u z : Fin 1 → ℝ) :
    rightFaceFlux g nf h u z 0 = rightWallFlux g nf (h 0) (u 0) (z 0) := rfl

private lemma leftFaceFlux_two_zero (g : ℝ)
    (nf : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ) (h u z : Fin 2 → ℝ) :
    leftFaceFlux g nf h u z 0 = leftWallFlux g nf (h 0) (u 0) (z 0) := rfl

private lemma rightFaceFlux_two_zero (g : ℝ)
    (nf : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ) (h u z : Fin 2 → ℝ) :
    rightFaceFlux g nf h u z 0 =
      leftFlux g nf (h 0) (u 0) (h 1) (u 1) (z 0) (z 1) := rfl

/-! ## B. Three unequal bed cells -/

/-- Face values on beds `(0, 2, 1)`, `η = 3`, `g = 2`: each cell sees
`9`, `1` and `4` on both of its faces. -/
example : leftWallFlux 2 (leftStateFlux 2) 3 0 0 = (0, 9) ∧
    leftFlux 2 (leftStateFlux 2) 3 0 1 0 0 2 = (0, 9) ∧
    rightFlux 2 (leftStateFlux 2) 3 0 1 0 0 2 = (0, 1) ∧
    leftFlux 2 (leftStateFlux 2) 1 0 2 0 2 1 = (0, 1) ∧
    rightFlux 2 (leftStateFlux 2) 1 0 2 0 2 1 = (0, 4) ∧
    rightWallFlux 2 (leftStateFlux 2) 2 0 1 = (0, 4) := by
  norm_num [leftWallFlux, rightWallFlux, leftFlux, rightFlux,
    interfaceFlux, faceState, faceDepth, leftStateFlux]

/-- All three unequal-bed cells are preserved at `Δt = 1/2`. -/
example : cellUpdate 2 (1 / 2) (fun _ => ⟨1, one_pos⟩) (leftStateFlux 2)
    ![3, 1, 2] ![0, 0, 0] ![0, 2, 1] 0 = (3, 0) := by
  rw [cellUpdate, rightFaceFlux_three_zero, leftFaceFlux_three_zero]
  norm_num [leftWallFlux, leftFlux, rightFlux, interfaceFlux, faceState,
    faceDepth, leftStateFlux]

example : cellUpdate 2 (1 / 2) (fun _ => ⟨1, one_pos⟩) (leftStateFlux 2)
    ![3, 1, 2] ![0, 0, 0] ![0, 2, 1] 1 = (1, 0) := by
  rw [cellUpdate, rightFaceFlux_three_one, leftFaceFlux_three_one]
  norm_num [leftFlux, rightFlux, interfaceFlux, faceState, faceDepth,
    leftStateFlux]

example : cellUpdate 2 (1 / 2) (fun _ => ⟨1, one_pos⟩) (leftStateFlux 2)
    ![3, 1, 2] ![0, 0, 0] ![0, 2, 1] 2 = (2, 0) := by
  rw [cellUpdate, rightFaceFlux_three_two, leftFaceFlux_three_two]
  norm_num [rightWallFlux, leftFlux, rightFlux, interfaceFlux, faceState,
    faceDepth, leftStateFlux]

/-- Swapping the interior orientation moves the middle momentum by `4`. -/
example :
    (1, 0) - ((1 / 2 : ℝ) / 1) •
      (leftFlux 2 (leftStateFlux 2) 1 0 2 0 2 1 -
        leftFlux 2 (leftStateFlux 2) 3 0 1 0 0 2) ≠ ((1 : ℝ), (0 : ℝ)) := by
  norm_num [leftFlux, interfaceFlux, faceState, faceDepth, leftStateFlux]

/-! ## C. Boundary and negative controls -/

/-- One wet rest cell between walls is preserved for arbitrary step data. -/
example : cellUpdate 3 7 (fun _ => ⟨1 / 3, by norm_num⟩) (leftStateFlux 3)
    ![2] ![0] ![5] 0 = (2, 0) := by
  rw [cellUpdate, rightFaceFlux_one_zero, leftFaceFlux_one_zero]
  norm_num [leftWallFlux, rightWallFlux, leftFlux, rightFlux,
    interfaceFlux, faceState, faceDepth, leftStateFlux]

/-- The wall identities at the concrete rest state `h = 3`, `g = 2`. -/
example : leftWallFlux 2 (leftStateFlux 2) 3 0 0 = (0, 9) ∧
    rightWallFlux 2 (leftStateFlux 2) 3 0 0 = (0, 9) := by
  have h : leftWallFlux 2 (leftStateFlux 2) 3 0 0 = (0, 2 * 3 ^ 2 / 2) ∧
      rightWallFlux 2 (leftStateFlux 2) 3 0 0 = (0, 2 * 3 ^ 2 / 2) :=
    wall_fluxes_eq_of_rest (leftStateFlux 2)
      (leftStateFlux_consistent 2) (by norm_num) (by norm_num)
  norm_num at h
  exact h

/-- Nonzero discharge on beds `(0, 1, 2)`: the middle depth `2 ↦ 3`. -/
example : (cellUpdate 2 1 (fun _ => ⟨1, one_pos⟩) (leftStateFlux 2)
    (fun i => 3 - ![0, 1, 2] i) (fun _ => 1) ![0, 1, 2] 1).1 = 3 := by
  rw [cellUpdate, rightFaceFlux_three_one, leftFaceFlux_three_one]
  norm_num [leftFlux, rightFlux, interfaceFlux, faceState, faceDepth,
    leftStateFlux]

/-- A wet-consistent flux that differs at the dry diagonal state. -/
private noncomputable def dryWitnessFlux (g : ℝ) :
    ℝ × ℝ → ℝ × ℝ → ℝ × ℝ :=
  fun p _ => (p.2, p.2 ^ 2 / p.1 + g * p.1 ^ 2 / 2 + (1 - p.1 / p.1))

/-- At beds `(0, 1)` with `η = 1`, the dry witness moves cell `0` to
`(1, -1)`. -/
example : cellUpdate 2 1 (fun _ => ⟨1, one_pos⟩) (dryWitnessFlux 2)
    (fun i => ![0, 1] 1 - ![0, 1] i) (fun _ => 0) ![0, 1] 0 = (1, -1) := by
  rw [cellUpdate, rightFaceFlux_two_zero, leftFaceFlux_two_zero]
  norm_num [leftWallFlux, leftFlux, rightFlux, interfaceFlux, faceState,
    faceDepth, dryWitnessFlux]

/-- Contrast: the left-state physical flux, also consistent at the dry
state `(0, 0)`, keeps that first cell at rest. -/
example : cellUpdate 2 1 (fun _ => ⟨1, one_pos⟩) (leftStateFlux 2)
    (fun i => ![0, 1] 1 - ![0, 1] i) (fun _ => 0) ![0, 1] 0 = (1, 0) := by
  rw [cellUpdate, rightFaceFlux_two_zero, leftFaceFlux_two_zero]
  norm_num [leftWallFlux, leftFlux, rightFlux, interfaceFlux, faceState,
    faceDepth, leftStateFlux]

#print axioms EarthScience.HydrostaticReconstruction.corrected_fluxes_eq_of_lake_at_rest
#print axioms EarthScience.HydrostaticReconstruction.wall_fluxes_eq_of_rest
#print axioms EarthScience.HydrostaticReconstruction.cellUpdate_eq_of_lake_at_rest
#print axioms EarthScience.HydrostaticReconstruction.cellUpdate_fst_eq_discreteBalance
#print axioms EarthScience.HydrostaticReconstruction.cellUpdate_fst_ne_of_uniform_flow
#print axioms EarthScience.HydrostaticReconstruction.exists_cellUpdate_ne_of_dry
