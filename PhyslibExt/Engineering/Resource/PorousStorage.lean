/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic

import Mathlib.Tactic.Ring

/-!
# Porous storage: pore inventory and saturation partition

## i. Overview

Storage bookkeeping for a rigid porous medium with bulk volume `V_bulk`,
porosity `phi`, phase saturations `S` over a finite phase type and phase
densities `rho`. The pore volume is `phi * V_bulk`, phase `i` occupies
`phi * V_bulk * S i` and carries mass `phi * V_bulk * S i * rho i`.
Superficial (Darcy) flux, volumetric flow and pore velocity are distinct
quantities and are kept distinct here.

## ii. Key results

- `PorousStorage.sum_phaseVolume_eq`: admissible saturations (nonnegative,
  summing to one) fill the pore volume, each between zero and the pore
  volume.
- `PorousStorage.sum_poreInventory`: the total phase mass factors as
  `phi * V_bulk * (sum of S i * rho i)`.
- `PorousStorage.phi_mul_poreVelocity`: pore velocity rescales the
  superficial flux by the porosity.

## iii. Table of contents

- A. Volumes, inventories and velocities

## iv. References

- F. A. L. Dullien, *Porous Media: Fluid Transport and Pore Structure*,
  2nd ed., Academic Press (1992), Chapter 1.
- `PhyslibExt/EarthScience/GroundwaterRetardation.lean`: linear-sorption
  storage bookkeeping in the same plain-real style.
-/

@[expose] public section

namespace Engineering.Resource.PorousStorage

/-- Pore volume of a bulk volume `V_bulk` at porosity `phi`. -/
def poreVolume (phi V_bulk : ℝ) : ℝ :=
  phi * V_bulk

/-- Volume occupied by phase `i`: `phi * V_bulk * S_i`. -/
def phaseVolume {ι : Type*} (phi V_bulk : ℝ) (S : ι → ℝ) (i : ι) : ℝ :=
  phi * V_bulk * S i

/-- Mass inventory (`poreInventory`) of phase `i`:
`phi * V_bulk * S_i * rho_i`. -/
def poreInventory {ι : Type*} (phi V_bulk : ℝ) (S rho : ι → ℝ) (i : ι) : ℝ :=
  phi * V_bulk * S i * rho i

/-- Phase masses are pore volumes times densities. -/
lemma poreInventory_eq {ι : Type*} (phi V_bulk : ℝ) (S rho : ι → ℝ) (i : ι) :
    poreInventory phi V_bulk S rho i = phaseVolume phi V_bulk S i * rho i := by
  rfl

/-- Phase volumes are nonnegative for nonnegative porosity, bulk volume and
saturations. -/
lemma phaseVolume_nonneg {ι : Type*} {phi V_bulk : ℝ} (hphi : 0 ≤ phi)
    (hV : 0 ≤ V_bulk) {S : ι → ℝ} (hS : ∀ i, 0 ≤ S i) (i : ι) :
    0 ≤ phaseVolume phi V_bulk S i := by
  unfold phaseVolume
  exact mul_nonneg (mul_nonneg hphi hV) (hS i)

/-- Phase masses are nonnegative for nonnegative porosity, bulk volume,
saturations and densities. -/
lemma poreInventory_nonneg {ι : Type*} {phi V_bulk : ℝ} (hphi : 0 ≤ phi)
    (hV : 0 ≤ V_bulk) {S rho : ι → ℝ} (hS : ∀ i, 0 ≤ S i)
    (hrho : ∀ i, 0 ≤ rho i) (i : ι) :
    0 ≤ poreInventory phi V_bulk S rho i := by
  unfold poreInventory
  exact mul_nonneg (mul_nonneg (mul_nonneg hphi hV) (hS i)) (hrho i)

set_option linter.unusedVariables false in
/-- **Saturation partition.** For admissible data (nonnegative porosity,
bulk volume, and saturations) with saturations summing to one, the phase
volumes are nonnegative volumes filling the pore volume:
`∑ i, phi * V_bulk * S_i = phi * V_bulk`. Nonnegativity is part of the
physical statement: signed weights summing to one, such as `(-1, 2)`, are
not saturations and are excluded here. -/
lemma sum_phaseVolume_eq {ι : Type*} [Fintype ι] {phi V_bulk : ℝ}
    (hphi : 0 ≤ phi) (hV : 0 ≤ V_bulk) {S : ι → ℝ} (hS0 : ∀ i, 0 ≤ S i)
    (hS : ∑ i, S i = 1) :
    ∑ i, phaseVolume phi V_bulk S i = poreVolume phi V_bulk := by
  unfold phaseVolume poreVolume
  simp only [← Finset.mul_sum, hS, mul_one]

/-- Each admissible saturation is at most one: a nonnegative family
summing to one has every term at most one. -/
lemma saturation_le_one {ι : Type*} [Fintype ι] {S : ι → ℝ}
    (hS0 : ∀ i, 0 ≤ S i) (hS : ∑ i, S i = 1) (i : ι) :
    S i ≤ 1 := by
  calc S i ≤ ∑ j, S j := Finset.single_le_sum (fun j _ => hS0 j) (Finset.mem_univ i)
    _ = 1 := hS

/-- Each admissible phase volume lies between zero and the pore volume. -/
lemma phaseVolume_le_poreVolume {ι : Type*} [Fintype ι] {phi V_bulk : ℝ}
    (hphi : 0 ≤ phi) (hV : 0 ≤ V_bulk) {S : ι → ℝ} (hS0 : ∀ i, 0 ≤ S i)
    (hS : ∑ i, S i = 1) (i : ι) :
    phaseVolume phi V_bulk S i ≤ poreVolume phi V_bulk := by
  have hSi : S i ≤ 1 := saturation_le_one hS0 hS i
  have hPV : 0 ≤ phi * V_bulk := mul_nonneg hphi hV
  unfold phaseVolume poreVolume
  calc phi * V_bulk * S i ≤ phi * V_bulk * 1 := mul_le_mul_of_nonneg_left hSi hPV
    _ = phi * V_bulk := mul_one _

/-- Total phase mass factors: `∑ i, m_i = phi * V_bulk * ∑ i, S_i * rho_i`. -/
lemma sum_poreInventory {ι : Type*} [Fintype ι] (phi V_bulk : ℝ)
    (S rho : ι → ℝ) :
    ∑ i, poreInventory phi V_bulk S rho i =
      phi * V_bulk * ∑ i, S i * rho i := by
  have h : ∀ i, poreInventory phi V_bulk S rho i = (phi * V_bulk) * (S i * rho i) := by
    intro i
    simp only [poreInventory]
    ring
  simp only [h, Finset.mul_sum]

/-- Superficial (Darcy) flux `u` from volumetric flow `Q` over bulk area
`A`: `u = Q / A`. Distinct from the pore velocity. At `A = 0` the value is
the totalized `0`, outside the physical domain; rewrite lemmas therefore
carry `A ≠ 0`. -/
noncomputable def superficialFlux (Q A : ℝ) : ℝ :=
  Q / A

/-- Pore (interstitial) velocity `v = u / phi` for superficial flux `u` and
porosity `phi`. Distinct from the superficial flux. At `phi = 0` the value
is the totalized `0`, outside the physical domain; rewrite lemmas
therefore carry `phi ≠ 0`. -/
noncomputable def poreVelocity (u phi : ℝ) : ℝ :=
  u / phi

/-- Volumetric flow from superficial flux and area: `Q = A * u`. -/
lemma volumetricFlow_eq (u A : ℝ) (hA : A ≠ 0) :
    A * superficialFlux (A * u) A = A * u := by
  unfold superficialFlux
  rw [mul_div_cancel_left₀ _ hA]

/-- The pore velocity rescales the superficial flux by porosity:
`phi * v = u` for `phi ≠ 0`. -/
lemma phi_mul_poreVelocity (u phi : ℝ) (hphi : phi ≠ 0) :
    phi * poreVelocity u phi = u := by
  unfold poreVelocity
  exact mul_div_cancel₀ _ hphi

end Engineering.Resource.PorousStorage
