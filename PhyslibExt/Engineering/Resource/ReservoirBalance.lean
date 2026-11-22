/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Basic.Real.Basic

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Single-phase reservoir inventory and pore-volume identification

## i. Overview

Single-phase isothermal reservoir inventory at constant pore volume `Vp`,
with the stipulated exponential density law
`rho(p) = rho0 * exp (cfl * (p - p0))` for reference density `rho0 > 0`
at pressure `p0` and fluid compressibility `cfl`. Produced mass on
depletion from `p0` to `p` is `Vp * (rho(p0) - rho(p))`. With known
`rho0` and `cfl` and a nonzero density change, the pore volume is
identified from produced mass; with no pressure excitation (`p = p0`) it
is not, and a linearized history identifies only the product `Vp * cfl`.
These are stipulated-law identities, not reserves inference.

## ii. Key results

- `ReservoirBalance.produced_mass_eq`: the produced-mass identity, with
  depletion positive and injection negative.
- `ReservoirBalance.porevolume_identified`: pore volume from produced
  mass under a nonzero pressure excursion.
- `ReservoirBalance.not_identified_at_initial`: zero excitation cannot
  distinguish pore volumes.
- `ReservoirBalance.linear_identifies_only_product`: a linearized history
  determines only `Vp * cfl`.

## iii. Table of contents

- A. Inventory and identification

## iv. References

- L. P. Dake, *Fundamentals of Reservoir Engineering*, Elsevier (1978),
  Chapter 3 (material balance for oil reservoirs).
-/

@[expose] public section

namespace Engineering.Resource.ReservoirBalance

/-! ## A. Inventory and identification -/

/-- Fluid density under the exponential compressibility law. -/
noncomputable def density (rho0 cfl p0 p : ℝ) : ℝ :=
  rho0 * Real.exp (cfl * (p - p0))

/-- Produced mass on depleting a constant pore volume `Vp` from `p0` to
`p`: initial inventory minus current inventory. In the physical regime
`0 < Vp`, `0 < rho0` and `0 < cfl` it is positive on depletion
(`p < p0`) and negative on injection (`p > p0`); outside that regime no
sign is claimed (zero pore volume gives zero, and negative parameters
reverse the sign). -/
noncomputable def producedMass (Vp rho0 cfl p0 p : ℝ) : ℝ :=
  Vp * (density rho0 cfl p0 p0 - density rho0 cfl p0 p)

/-- Linearized produced mass `Vp * rho0 * cfl * (p0 - p)` from the
first-order density approximation. A linearized history sees only the
product `Vp * cfl`. -/
noncomputable def linearProducedMass (Vp rho0 cfl p0 p : ℝ) : ℝ :=
  Vp * rho0 * cfl * (p0 - p)

/-- The density law returns the reference density at `p0`. -/
lemma density_at_initial (rho0 cfl p0 : ℝ) :
    density rho0 cfl p0 p0 = rho0 := by
  unfold density
  simp

/-- **Produced mass identity.**
`ΔM = Vp * rho0 * (1 - exp (cfl * (p - p0)))`. -/
lemma produced_mass_eq (Vp rho0 cfl p0 p : ℝ) :
    producedMass Vp rho0 cfl p0 p =
      Vp * rho0 * (1 - Real.exp (cfl * (p - p0))) := by
  have h := density_at_initial rho0 cfl p0
  unfold producedMass
  rw [h]
  unfold density
  ring

/-- Depletion produces positive mass. -/
lemma produced_mass_pos {Vp rho0 cfl p0 p : ℝ} (hVp : 0 < Vp)
    (hrho : 0 < rho0) (hcfl : 0 < cfl) (hp : p < p0) :
    0 < producedMass Vp rho0 cfl p0 p := by
  rw [produced_mass_eq]
  have harg : cfl * (p - p0) < 0 :=
    mul_neg_of_pos_of_neg hcfl (sub_neg.mpr hp)
  have hexp : Real.exp (cfl * (p - p0)) < 1 :=
    Real.exp_lt_one_iff.mpr harg
  have h1 : 0 < 1 - Real.exp (cfl * (p - p0)) := sub_pos.mpr hexp
  have hVR : 0 < Vp * rho0 := mul_pos hVp hrho
  exact mul_pos hVR h1

/-- Injection (pressure increase) gives negative produced mass: the sign
convention distinguishes production from injection. -/
lemma produced_mass_neg_of_pressure_increase {Vp rho0 cfl p0 p : ℝ}
    (hVp : 0 < Vp) (hrho : 0 < rho0) (hcfl : 0 < cfl) (hp : p0 < p) :
    producedMass Vp rho0 cfl p0 p < 0 := by
  rw [produced_mass_eq]
  have harg : 0 < cfl * (p - p0) := mul_pos hcfl (sub_pos.mpr hp)
  have hexp : 1 < Real.exp (cfl * (p - p0)) :=
    Real.one_lt_exp_iff.mpr harg
  have h1 : 1 - Real.exp (cfl * (p - p0)) < 0 := sub_neg.mpr hexp
  have hVR : 0 < Vp * rho0 := mul_pos hVp hrho
  exact mul_neg_of_pos_of_neg hVR h1

/-- No pressure change, no production. -/
lemma produced_mass_zero_at_initial (Vp rho0 cfl p0 : ℝ) :
    producedMass Vp rho0 cfl p0 p0 = 0 := by
  unfold producedMass
  simp

/-- **Pore-volume identification.** With known `rho0` and `cfl` and a
nonzero pressure excursion, produced mass determines the pore volume:
`Vp = ΔM / (rho0 * (1 - exp (cfl * (p - p0))))`. -/
lemma porevolume_identified {Vp rho0 cfl p0 p ΔM : ℝ} (hrho : 0 < rho0)
    (hcfl : 0 < cfl) (hp : p ≠ p0)
    (hΔ : ΔM = producedMass Vp rho0 cfl p0 p) :
    Vp = ΔM / (rho0 * (1 - Real.exp (cfl * (p - p0)))) := by
  have hcfl_ne : cfl ≠ 0 := ne_of_gt hcfl
  have hsub_ne : p - p0 ≠ 0 := sub_ne_zero.mpr hp
  have harg_ne : cfl * (p - p0) ≠ 0 := mul_ne_zero hcfl_ne hsub_ne
  have hexp_ne : Real.exp (cfl * (p - p0)) ≠ 1 := by
    intro hcon
    have hz : cfl * (p - p0) = 0 := (Real.exp_eq_one_iff _).mp hcon
    exact harg_ne hz
  have h1_ne : (1 - Real.exp (cfl * (p - p0))) ≠ 0 := by
    intro hcon
    apply hexp_ne
    linarith
  have hrho_ne : rho0 ≠ 0 := ne_of_gt hrho
  have hne : rho0 * (1 - Real.exp (cfl * (p - p0))) ≠ 0 :=
    mul_ne_zero hrho_ne h1_ne
  rw [eq_div_iff hne, hΔ, produced_mass_eq]
  ring

/-- **Zero-excitation non-identification.** At `p = p0`, two different
pore volumes give the same (zero) produced mass, so pore volume cannot
be identified without a pressure excursion. -/
lemma not_identified_at_initial {rho0 cfl p0 : ℝ} :
    producedMass 1 rho0 cfl p0 p0 = producedMass 2 rho0 cfl p0 p0 ∧
      (1 : ℝ) ≠ 2 := by
  refine ⟨?_, by norm_num⟩
  rw [produced_mass_zero_at_initial, produced_mass_zero_at_initial]

/-- A linearized history identifies only the product `Vp * cfl`: two
parameter pairs with the same product give identical linearized produced
mass at every pressure. -/
lemma linear_identifies_only_product {Vp1 Vp2 c1 c2 rho0 p0 p : ℝ}
    (h : Vp1 * c1 = Vp2 * c2) :
    linearProducedMass Vp1 rho0 c1 p0 p =
      linearProducedMass Vp2 rho0 c2 p0 p := by
  unfold linearProducedMass
  calc Vp1 * rho0 * c1 * (p0 - p)
      = (Vp1 * c1) * (rho0 * (p0 - p)) := by ring
    _ = (Vp2 * c2) * (rho0 * (p0 - p)) := by rw [h]
    _ = Vp2 * rho0 * c2 * (p0 - p) := by ring

/-- **Product identification, both directions.** Under a nondegenerate
observation (nonzero reference density and a nonzero pressure excursion),
equal linearized produced mass is equivalent to equal products
`Vp * cfl`: the linearized history determines exactly the product, no
more and no less. -/
lemma linearProducedMass_eq_iff {Vp1 Vp2 c1 c2 rho0 p0 p : ℝ}
    (hrho : rho0 ≠ 0) (hp : p ≠ p0) :
    linearProducedMass Vp1 rho0 c1 p0 p =
        linearProducedMass Vp2 rho0 c2 p0 p ↔
      Vp1 * c1 = Vp2 * c2 := by
  unfold linearProducedMass
  have hd : p0 - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hp)
  have hfac : rho0 * (p0 - p) ≠ 0 := mul_ne_zero hrho hd
  constructor
  · intro h
    have h' : (Vp1 * c1) * (rho0 * (p0 - p)) =
        (Vp2 * c2) * (rho0 * (p0 - p)) := by
      calc (Vp1 * c1) * (rho0 * (p0 - p))
          = Vp1 * rho0 * c1 * (p0 - p) := by ring
        _ = Vp2 * rho0 * c2 * (p0 - p) := h
        _ = (Vp2 * c2) * (rho0 * (p0 - p)) := by ring
    exact mul_right_cancel₀ hfac h'
  · intro h
    calc Vp1 * rho0 * c1 * (p0 - p)
        = (Vp1 * c1) * (rho0 * (p0 - p)) := by ring
      _ = (Vp2 * c2) * (rho0 * (p0 - p)) := by rw [h]
      _ = Vp2 * rho0 * c2 * (p0 - p) := by ring

end Engineering.Resource.ReservoirBalance
