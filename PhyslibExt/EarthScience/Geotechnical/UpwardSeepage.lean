/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.EarthScience.Geotechnical.UnitWeights
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Upward-seepage effective-stress threshold

## i. Overview

Depth `z ≥ 0` is measured downward from the top surface of a
uniform saturated column. Gauge pore pressure is zero at the
top. Steady upward flow has the supplied linear total-head
profile `h(z) = i * z` with uniform gradient `i ≥ 0` (head
increases with depth for upward flow in depth coordinates);
Darcy's law is not derived. The compression-positive
effective stress is `σ'(z) = z * (γ_sub - i * γw)`, nonnegative
at every positive depth exactly at or below the critical
gradient `(Gs - 1) / (1 + e)`.

## ii. Key results

- `EarthScience.porePressureOfHead` and `upwardHead`: pore
  pressure from total head and the linear upward head.
- `EarthScience.upwardSeepage_effectiveStress`: the linear
  effective-stress profile.
- `EarthScience.upwardSeepage_nonneg_iff` and
  `upwardSeepage_nonneg_total_iff`: the critical-gradient
  threshold, in closed form and on total minus pore stress.

## iii. Table of contents

- A. Head, pore pressure, and effective stress
- B. Critical-gradient threshold

## iv. References

- `PhyslibExt.EarthScience.Geotechnical.UnitWeights` for
  `bulkUnitWeight` and `submergedUnitWeight`.
- `PhyslibExt.EarthScience.HydrostaticColumn` for the
  depth-coordinate hydrostatic profile checked against
  the no-flow case in tests (not imported here).
- J. A. Knappett and R. F. Craig, *Craig's Soil Mechanics*,
  9th edition, CRC Press, 2019: upward seepage and the
  critical hydraulic gradient.
-/

@[expose] public section

namespace EarthScience

/-! ## A. Head, pore pressure, and effective stress -/

/-- Pore pressure from total head: pressure head is total head
minus elevation, and elevation is `-z` for downward depth `z`
with the top surface as datum. -/
noncomputable def porePressureOfHead (γw h z : ℝ) : ℝ := γw * (h + z)

/-- Linear upward-flow head profile, zero at the top surface. -/
noncomputable def upwardHead (i z : ℝ) : ℝ := i * z

/-- Gauge pore pressure vanishes at the top surface. -/
lemma upwardSeepage_porePressure_top (γw i : ℝ) :
    porePressureOfHead γw (upwardHead i 0) 0 = 0 := by
  simp [porePressureOfHead, upwardHead]

/-- Conditional form of the effective-stress profile, given
the canonical submerged-weight bridge. -/
private lemma upwardSeepage_effectiveStress_of
    (hsub : ∀ {Gs e γw : ℝ}, (1 : ℝ) + e ≠ 0 →
      submergedUnitWeight Gs e γw = bulkUnitWeight Gs 1 e γw - γw)
    {Gs e γw i z : ℝ} (he : 1 + e ≠ 0) :
    bulkUnitWeight Gs 1 e γw * z - porePressureOfHead γw (upwardHead i z) z
      = z * (submergedUnitWeight Gs e γw - i * γw) := by
  have h := hsub (Gs := Gs) (e := e) (γw := γw) he
  unfold porePressureOfHead upwardHead
  rw [h]
  ring

/-- Effective stress under upward seepage:
`σ'(z) = z * (γ_sub - i * γw)`. -/
theorem upwardSeepage_effectiveStress {Gs e γw i z : ℝ}
    (he : 1 + e ≠ 0) :
    bulkUnitWeight Gs 1 e γw * z - porePressureOfHead γw (upwardHead i z) z
      = z * (submergedUnitWeight Gs e γw - i * γw) :=
  upwardSeepage_effectiveStress_of
    (fun he => submerged_eq_sat_sub_water he) he

/-- The submerged-to-water unit-weight ratio is
`(Gs - 1) / (1 + e)`. -/
lemma submergedUnitWeight_div_water {Gs e γw : ℝ} (hγ : γw ≠ 0) :
    submergedUnitWeight Gs e γw / γw = (Gs - 1) / (1 + e) := by
  unfold submergedUnitWeight
  rw [div_right_comm, mul_div_cancel_right₀ _ hγ]

/-- With no flow, the pore pressure is hydrostatic: `γw * z`. -/
lemma porePressureOfHead_upwardHead_zero (γw z : ℝ) :
    porePressureOfHead γw (upwardHead 0 z) z = γw * z := by
  simp [porePressureOfHead, upwardHead]

/-- No-flow pore pressure is the depth-coordinate hydrostatic
profile at unit density factor `γw = ρ * g`. -/
lemma porePressureOfHead_upwardHead_zero_eq_hydrostatic (ρ g z : ℝ) :
    porePressureOfHead (ρ * g) (upwardHead 0 z) z
      = (fun d => (0 : ℝ) + ρ * g * d) z := by
  rw [porePressureOfHead_upwardHead_zero]
  ring

/-! ## B. Critical-gradient threshold -/

/-- Main result: effective stress is nonnegative at every
positive depth exactly when `i ≤ (Gs - 1) / (1 + e)`. The
premises `_hi` and `_he` mark the physical domain (upward
flow, nonnegative void ratio, so the critical gradient is
the source formula's value, not its totalized value at the
singular `e = -1`); the equivalence itself is algebraic
in `i`. -/
theorem upwardSeepage_nonneg_iff {Gs e γw i : ℝ} (hγ : 0 < γw)
    (_hi : 0 ≤ i) (_he : 0 ≤ e) :
    (∀ z > 0, 0 ≤ z * (submergedUnitWeight Gs e γw - i * γw)) ↔
      i ≤ (Gs - 1) / (1 + e) := by
  have hratio : submergedUnitWeight Gs e γw / γw = (Gs - 1) / (1 + e) :=
    submergedUnitWeight_div_water (ne_of_gt hγ)
  rw [← hratio]
  constructor
  · intro h
    have h1 := h 1 one_pos
    rw [one_mul] at h1
    rw [le_div_iff₀ hγ]
    linarith
  · intro h z hz
    have hc : 0 ≤ submergedUnitWeight Gs e γw - i * γw := by
      have hle := (le_div_iff₀ hγ).mp h
      linarith
    exact mul_nonneg (le_of_lt hz) hc

/-- Conditional form of the total-stress threshold, given the
canonical submerged-weight bridge. -/
private lemma upwardSeepage_nonneg_total_iff_of
    (hsub : ∀ {Gs e γw : ℝ}, (1 : ℝ) + e ≠ 0 →
      submergedUnitWeight Gs e γw = bulkUnitWeight Gs 1 e γw - γw)
    {Gs e γw i : ℝ} (he : 1 + e ≠ 0) (hγ : 0 < γw) (_hi : 0 ≤ i)
    (_he : 0 ≤ e) :
    (∀ z > 0, 0 ≤ bulkUnitWeight Gs 1 e γw * z
        - porePressureOfHead γw (upwardHead i z) z) ↔
      i ≤ (Gs - 1) / (1 + e) := by
  have heff : ∀ z : ℝ, bulkUnitWeight Gs 1 e γw * z
      - porePressureOfHead γw (upwardHead i z) z
      = z * (submergedUnitWeight Gs e γw - i * γw) :=
    fun z => upwardSeepage_effectiveStress_of hsub he
  simp_rw [heff]
  exact upwardSeepage_nonneg_iff hγ _hi _he

/-- The threshold stated on total stress minus pore pressure
(requires `1 + e ≠ 0` for the submerged-weight bridge, on
the physical void-ratio domain `0 ≤ e`). -/
theorem upwardSeepage_nonneg_total_iff {Gs e γw i : ℝ}
    (he : 1 + e ≠ 0) (hγ : 0 < γw) (_hi : 0 ≤ i) (_he : 0 ≤ e) :
    (∀ z > 0, 0 ≤ bulkUnitWeight Gs 1 e γw * z
        - porePressureOfHead γw (upwardHead i z) z) ↔
      i ≤ (Gs - 1) / (1 + e) :=
  upwardSeepage_nonneg_total_iff_of
    (fun he => submerged_eq_sat_sub_water he) he hγ _hi _he

end EarthScience
