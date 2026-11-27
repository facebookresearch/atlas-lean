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

public import PhyslibExt.EarthScience.PoreVelocity

import Mathlib.Tactic.Ring

/-!
# Porous storage: pore inventory and saturation partition

## i. Overview

Storage bookkeeping for a rigid porous medium with bulk volume `V_bulk`,
porosity `phi`, phase saturations `S` over a finite phase type and phase
densities `rho`. The pore volume is `phi * V_bulk`, phase `i` occupies
`phi * V_bulk * S i` and carries mass `phi * V_bulk * S i * rho i`.
The superficial (Darcy) flux `u = Q / A` of a volumetric flow `Q` through
bulk area `A` is defined here, with the volumetric-flow law `Q = A * u`
for any flow and nonzero area; pore velocity itself is the imported
`EarthScience.poreVelocity`, `v = u / phi`, kept distinct from the
superficial flux. That conversion divides by the whole pore fraction
`phi`: it gives the velocity of a fluid filling the pore space, or, from
the total flux of all phases, their velocity averaged over the whole pore
space; it is not the velocity of an individual phase, which occupies only
the fraction `phi * S i` of the bulk volume.

## ii. Key results

- `PorousStorage.sum_phaseVolume_eq`: for weights summing to one, the
  phase volumes add up to the pore volume.
- `PorousStorage.phaseVolume_nonneg` and
  `PorousStorage.phaseVolume_le_poreVolume`: for nonnegative porosity and
  bulk volume and admissible saturations (nonnegative, summing to one),
  each phase volume lies between zero and the pore volume.
- `PorousStorage.sum_poreInventory`: the total phase mass factors as
  `phi * V_bulk * (sum of S i * rho i)`.
- `PorousStorage.volumetricFlow_eq`: area times the superficial flux of
  any flow `Q` through a nonzero area recovers `Q`.
- `EarthScience.poreVelocity_mul` (imported): pore velocity rescales the
  superficial flux by the porosity. This is the velocity of a fluid filling
  the pore space, or the whole-pore average velocity from the total flux,
  not the velocity of an individual phase.

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

/-! ## A. Pore volumes and mass inventory -/

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

/-- Phase masses are phase volumes times densities. -/
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

/-- **Saturation partition.** For weights summing to one, the phase
volumes fill the pore volume:
`∑ i, phi * V_bulk * S_i = phi * V_bulk`. This sum identity is purely
algebraic: it needs only that the weights sum to one and also holds for
signed weights such as `(-1, 2)`. The physical partition content —
nonnegative phase volumes bounded by the pore volume — is the separate
admissibility lemmas below, whose hypotheses signed weights fail. -/
lemma sum_phaseVolume_eq {ι : Type*} [Fintype ι] {phi V_bulk : ℝ}
    {S : ι → ℝ} (hS : ∑ i, S i = 1) :
    ∑ i, phaseVolume phi V_bulk S i = poreVolume phi V_bulk := by
  unfold phaseVolume poreVolume
  simp only [← Finset.mul_sum, hS, mul_one]

/-- Each admissible saturation is at most one: a nonnegative family
summing to one has every term at most one. Mathlib's bundled form,
`StdSimplex.weights_apply_le_one`, takes finitely supported weights; this
is the plain-function form the phase-volume bound uses. -/
lemma saturation_le_one {ι : Type*} [Fintype ι] {S : ι → ℝ}
    (hS0 : ∀ i, 0 ≤ S i) (hS : ∑ i, S i = 1) (i : ι) :
    S i ≤ 1 := by
  calc S i ≤ ∑ j, S j := Finset.single_le_sum (fun j _ => hS0 j) (Finset.mem_univ i)
    _ = 1 := hS

/-- Each admissible phase volume is at most the pore volume:
`phi * V_bulk * S_i ≤ phi * V_bulk`. The matching lower bound is
`phaseVolume_nonneg`. -/
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

/-- Volumetric flow from superficial flux and area: `Q = A * u` with
`u = superficialFlux Q A`, for any volumetric flow `Q` and nonzero area
`A`. -/
lemma volumetricFlow_eq (Q A : ℝ) (hA : A ≠ 0) :
    A * superficialFlux Q A = Q := by
  unfold superficialFlux
  exact mul_div_cancel₀ Q hA

/-- The special case of `volumetricFlow_eq` for a flow written as `A * u`. -/
lemma volumetricFlow_eq_mul (u A : ℝ) (hA : A ≠ 0) :
    A * superficialFlux (A * u) A = A * u :=
  volumetricFlow_eq (A * u) A hA

end Engineering.Resource.PorousStorage
