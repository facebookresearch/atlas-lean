/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Order.Monotone.Defs
public import MathlibExt.Analysis.ODE.ContinuumBalances
public import PhyslibExt.ContinuumMechanics.ControlVolumes
public import PhyslibExt.EarthScience.ThiemWellFlow

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Radial Darcy head profile, well sources in a finite-volume ledger, and fractional flow

The steady radial Darcy discharge of a confined aquifer integrates to the logarithmic head
profile on an annulus around a well; with the sign of its rate reversed, this is the Thiem
profile. On a fixed chain of finite volumes, wells and open boundary faces enter an exact mass and
energy ledger. An explicit upwind fractional-flow update of a water-oil displacement with an
inflow boundary keeps the mobile saturation range under its CFL condition, and its water volume
changes by the inflow minus the outflow.

## i. Overview

A confined aquifer of constant transmissivity `Tr > 0` (hydraulic conductivity times aquifer
thickness) carries steady single-phase radial flow on the annulus `r0 ≤ r ≤ r1` around a well
of radius `r0 > 0`. Darcy's law is a constitutive input, not a derived fluid law: integrated
over the aquifer thickness and the circle of radius `r`, it gives the outward volumetric
discharge `Q = -2 π r Tr h'(r)` for the hydraulic head `h`. In steady flow without recharge in
the annulus the discharge is the same at every radius; `Q > 0` is injection and `Q < 0` is
extraction. Integrating `h' = -Q / (2 π Tr r)` gives
`h r - h r0 = -Q log (r / r0) / (2 π Tr)`.

The Thiem head difference `EarthScience.thiem_head_difference` is written for the profile
`C + Q log r / (2 π T)` with the pumping (extraction) rate `Q`, which is the negative of the
outward discharge: the profile with rate `P` has outward discharge `-P`. With the rate `-Q`
the Thiem head difference is exactly the radial Darcy head difference.

A zero well radius admits no head that stays finite at the axis with a nonzero discharge, and
a negative transmissivity sends the discharge up the head gradient; both inputs are rejected.
Multiphase flow, unconfined aquifers, leakage, recharge and transient storage are not treated.

Well and boundary sources (sections D-E). A fixed one-dimensional chain of `n` cells of common
positive volume `Δx` (per unit cross-section) carries signed face fluxes `F : Fin (n + 1) → ℝ`,
positive towards increasing index, as in `MathlibExt.Analysis.ODE.ContinuumBalances`. There is one
flux per face, so every interior face is shared by its two cells with the same signed value; the
exterior faces `0` and `Fin.last n` may carry nonzero fluxes. A cell may hold a well with signed
rate `q i` (injection `q i > 0`, production `q i < 0`). The cell rate is the transport rate
`discreteBalance Δx F i` plus `q i / Δx`, and one explicit step of length `dt` changes the stock
`Δx * ∑ i, c i` by `dt ((F 0 - F (Fin.last n)) + ∑ i, q i)`: the interior fluxes cancel
(`totalDiscreteChange_eq`). The ledger is applied with the same face mass fluxes `Fm` to mass,
with well mass rates `qI i - qP i`, and to energy, with the enthalpy flux `Fm j * h_j`
(`h = e + p / ρ` the energy-port enthalpy `ControlVolumes.specificEnthalpy`, flow work counted
once) and the well energy rate `qI i * hI i - qP i * h_i`: the produced fluid leaves at the
production mass rate `qP i` with the cell's own enthalpy. That enthalpy is the stored cell state's:
the cell stores the fluid mass `m i = φ i * ρc i` per unit volume (porosity `φ i > 0`) and the
fluid energy `E i = m i * ec i`, so `h_i = (E i + φ i * pc i) / m i` (`wellEnergyRate_eq_stored`).
No rock energy is stored, and the cell pressure `pc i` is an input (no equation of state is
assumed). The face states are free: interior face values cancel, and exterior ones are boundary
data. Face and cell densities are positive, as
`ControlVolumes.portEnergyRate_eq_massFlow` requires `ρ ≠ 0`: at `ρ = 0`, Lean's `x / 0 = 0`
would drop the flow work from the enthalpy. This is accounting only: no positivity of the
stocks, monotonicity or convergence is claimed. The no-flux specialization
`sum_add_mul_discreteBalance_of_noFlux` conserves the stock and so cannot represent an open chain
with wells and an outlet.

Fractional flow (sections F-H). One-dimensional water-oil displacement through a chain of `n + 1`
cells of length `dx`, cross-section `A` and porosity `φ` (pore volume `φ * A * dx > 0` per cell),
at total volumetric rate `Q ≥ 0` towards increasing index. The water saturation `S` is normalized
on the mobile range `[Swc, 1 - Sor]` (connate water `Swc`, residual oil `Sor`,
`ΔS = 1 - Sor - Swc > 0`) as `s = (S - Swc) / ΔS`. With the relative permeabilities `s ^ 2`
(water) and `(1 - s) ^ 2` (oil) and positive viscosities `μo`, `μw`, the water fractional flow
`f s = μo * s ^ 2 / (μo * s ^ 2 + μw * (1 - s) ^ 2)` increases on `[0, 1]` from `f 0 = 0` to
`f 1 = 1`, with derivative at most `B = (μo + μw) ^ 2 / (2 μo μw)`. The explicit upwind step moves
the water volume `Q dt f` through each face from the cell on its left; the left boundary face
carries the inflow state. In normalized variables cell `i` updates by
`s_i ↦ s_i - ν (f s_i - f s_(i-1))`, with `s_(-1)` the inflow state and
`ν = Q dt / (φ A dx ΔS)`; the `ΔS` comes from the normalization. Under `0 ≤ ν B ≤ 1` the update is
monotone in both arguments and keeps `[0, 1]`, equivalently `[Swc, 1 - Sor]`. The step is the
finite-volume step with upwind face fluxes, so the interior fluxes cancel
(`totalDiscreteChange_eq`) and the water volume changes by the inlet water volume `Q dt f (s_in)`
minus the outlet water volume `Q dt f (s_out)`; a periodic conservation identity would miss both
boundary terms. This is a model statement: no convergence, entropy condition or capillary
pressure is claimed.

## ii. Key results

- `EarthScience.radialDarcy_head_sub`: the radial Darcy head difference on the annulus.
- `EarthScience.radialDarcyHead_solves`: the logarithmic profile solves the model for every
  discharge.
- `EarthScience.thiemProfile_outward_discharge`: the Thiem rate is minus the outward
  discharge.
- `EarthScience.radialDarcy_head_sub_eq_thiem`: the head difference is the Thiem head
  difference for the pumping rate `-Q`.
- `EarthScience.radialDarcy_no_head_at_axis`: a zero well radius is rejected.
- `EarthScience.radialDischarge_upgradient_of_neg`: a negative transmissivity is rejected.
- `EarthScience.stock_add_mul_wellCellRate`: the cell rates sum to `totalDiscreteChange` plus the
  wells, and the stock changes by `dt` times the net boundary inflow plus the well total.
- `EarthScience.wellEnergyRate_eq_stored`: the produced enthalpy is fixed by the stored mass and
  energy, the porosity and the cell pressure.
- `EarthScience.well_boundary_ledger`: the mass and the energy ledger with shared face fluxes and
  production at the production mass rate with the enthalpy of the stored cell state.
- `EarthScience.fracFlow_zero_one`, `EarthScience.hasDerivAt_fracFlow`,
  `EarthScience.fracFlowDeriv_mem_Icc`, `EarthScience.fracFlow_sub_mem_Icc`,
  `EarthScience.monotoneOn_fracFlow`: end values, derivative, derivative bound, Lipschitz bound and
  monotonicity of the fractional flow on `[0, 1]`.
- `EarthScience.upwindUpdate_mono`, `EarthScience.upwindStep_mem_Icc`: the update is monotone and
  keeps `[0, 1]` under `0 ≤ ν B ≤ 1`.
- `EarthScience.normSat_mem_Icc_iff`, `EarthScience.normSat_satStep`,
  `EarthScience.satStep_mem_Icc`: the physical step normalizes to the update with
  `ν = Q dt / (φ A dx ΔS)` and keeps `[Swc, 1 - Sor]`.
- `EarthScience.upwindStep_eq_discreteBalance`, `EarthScience.sum_upwindStep`,
  `EarthScience.satStep_volume_balance`: the conservative form and the inlet-minus-outlet balance.

## iii. Table of contents

- A. Radial Darcy head profile
- B. Matching the Thiem profile
- C. Rejected inputs
- D. Cells with wells
- E. Mass and energy ledgers
- F. Fractional flow
- G. Normalized saturation and the CFL number
- H. The upwind step: monotonicity, interval and balance

## iv. References

- J. Bear, *Dynamics of Fluids in Porous Media*, American Elsevier (1972): Darcy's law and
  steady radial flow to a well in a confined aquifer.
- `EarthScience.thiem_head_difference` (`PhyslibExt.EarthScience.ThiemWellFlow`).
- J. Bear, *Dynamics of Fluids in Porous Media*, American Elsevier (1972): mass and energy
  balances with sources and sinks in porous media.
- R. J. LeVeque, *Finite Volume Methods for Hyperbolic Problems*, Cambridge University Press
  (2002), ch. 4: conservative finite-volume updates, whose interior fluxes cancel in the total;
  ch. 12: upwind methods for nonlinear scalar conservation laws, the CFL condition and monotone
  methods.
- S. E. Buckley and M. C. Leverett, *Mechanism of fluid displacement in sands*, Trans. AIME 146
  (1942): fractional flow and one-dimensional displacement.
- L. P. Dake, *Fundamentals of Reservoir Engineering*, Elsevier (1978), ch. 10: fractional flow
  with normalized saturation and relative permeabilities.
- `MathlibExt.Analysis.ODE.ContinuumBalances.totalDiscreteChange_eq`
  (`MathlibExt.Analysis.ODE.ContinuumBalances`) and `ControlVolumes.specificEnthalpy`
  (`PhyslibExt.ContinuumMechanics.ControlVolumes`).
-/

@[expose] public section

namespace EarthScience

/-! ## A. Radial Darcy head profile -/

/-- Radial Darcy head profile with head `h0` at the well radius `r0`, constant outward
discharge `Q` and transmissivity `Tr`: `h0 - Q log (r / r0) / (2 π Tr)`. -/
noncomputable def radialDarcyHead (h0 Q Tr r0 r : ℝ) : ℝ :=
  h0 - Q * Real.log (r / r0) / (2 * Real.pi * Tr)

/-- Radial Darcy head difference on the annulus `r0 ≤ r ≤ r1` with `r0 > 0` and constant
transmissivity `Tr > 0`. If the head `h` is continuous on the closed annulus, has radial
derivative `h'` inside it, and the steady outward discharge `Q = -2 π r Tr h'(r)` is the same
at every interior radius, then `h r - h r0 = -Q log (r / r0) / (2 π Tr)` on the closed
annulus. -/
lemma radialDarcy_head_sub {h h' : ℝ → ℝ} {Q Tr r0 r1 : ℝ} (hr0 : 0 < r0) (hTr : 0 < Tr)
    (hcont : ContinuousOn h (Set.Icc r0 r1))
    (hderiv : ∀ r ∈ Set.Ioo r0 r1, HasDerivAt h (h' r) r)
    (hQ : ∀ r ∈ Set.Ioo r0 r1, Q = -2 * Real.pi * r * Tr * h' r) :
    ∀ r ∈ Set.Icc r0 r1, h r - h r0 = -Q * Real.log (r / r0) / (2 * Real.pi * Tr) := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hr0' : r0 ≠ 0 := ne_of_gt hr0
  have hTr' : Tr ≠ 0 := ne_of_gt hTr
  have h2Tr : (2 * Real.pi * Tr) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hpi) hTr'
  intro r hr
  have hr0r : r0 ≤ r := hr.1
  have hrr1 : r ≤ r1 := hr.2
  by_cases heq : r = r0
  · rw [heq]
    simp only [sub_self]
    have hdiv : r0 / r0 = 1 := by field_simp
    rw [hdiv, Real.log_one]
    simp
  · have hlt : r0 < r := lt_of_le_of_ne hr0r (fun h => heq h.symm)
    have hrne : r - r0 ≠ 0 := by
      apply ne_of_gt
      linarith
    have hrpos : 0 < r := lt_trans hr0 hlt
    have hr' : r ≠ 0 := ne_of_gt hrpos
    have hsub1 : Set.Icc r0 r ⊆ Set.Icc r0 r1 :=
      Set.Icc_subset_Icc_right hrr1
    have hsub0 : Set.Icc r0 r ⊆ {0}ᶜ := by
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      have hx0 : r0 ≤ x := hx.1
      have : 0 < x := lt_of_lt_of_le hr0 hx0
      exact ne_of_gt this
    have hcont_h : ContinuousOn h (Set.Icc r0 r) := hcont.mono hsub1
    have hcont_log : ContinuousOn Real.log (Set.Icc r0 r) :=
      Real.continuousOn_log.mono hsub0
    have hcont_Qlog : ContinuousOn (fun s : ℝ => Q * Real.log s) (Set.Icc r0 r) :=
      hcont_log.const_mul Q
    have hcont_g2 :
        ContinuousOn (fun s : ℝ => Q * Real.log s / (2 * Real.pi * Tr)) (Set.Icc r0 r) :=
      hcont_Qlog.div_const (2 * Real.pi * Tr)
    have hcont_g :
        ContinuousOn (fun s : ℝ => h s + Q * Real.log s / (2 * Real.pi * Tr)) (Set.Icc r0 r) :=
      hcont_h.add hcont_g2
    have hderiv_zero : ∀ x ∈ Set.Ioo r0 r,
        HasDerivAt (fun s : ℝ => h s + Q * Real.log s / (2 * Real.pi * Tr)) 0 x := by
      intro x hx
      have hx0 : r0 < x := hx.1
      have hxx : x < r := hx.2
      have hxpos : 0 < x := lt_trans hr0 hx0
      have hx' : x ≠ 0 := ne_of_gt hxpos
      have hx1 : x ∈ Set.Ioo r0 r1 := ⟨hx0, lt_of_lt_of_le hxx hrr1⟩
      have hh : HasDerivAt h (h' x) x := hderiv x hx1
      have hQx : Q = -2 * Real.pi * x * Tr * h' x := hQ x hx1
      have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx'
      have hQm : HasDerivAt (fun s : ℝ => Q * Real.log s) (Q * x⁻¹) x :=
        hlog.const_mul Q
      have hdiv2 : HasDerivAt (fun s : ℝ => Q * Real.log s / (2 * Real.pi * Tr))
          ((Q * x⁻¹) / (2 * Real.pi * Tr)) x :=
        hQm.div_const (2 * Real.pi * Tr)
      have heq2 : (Q * x⁻¹) / (2 * Real.pi * Tr) = Q / (2 * Real.pi * Tr * x) := by
        field_simp
      rw [heq2] at hdiv2
      have hadd : HasDerivAt (fun s : ℝ => h s + Q * Real.log s / (2 * Real.pi * Tr))
          (h' x + Q / (2 * Real.pi * Tr * x)) x :=
        hh.add hdiv2
      have hzero : h' x + Q / (2 * Real.pi * Tr * x) = 0 := by
        rw [hQx]
        field_simp
        ring
      rw [hzero] at hadd
      exact hadd
    obtain ⟨c, hc_mem, hc_eq⟩ := exists_hasDerivAt_eq_slope
      (fun s : ℝ => h s + Q * Real.log s / (2 * Real.pi * Tr)) (fun _ => 0) hlt hcont_g hderiv_zero
    have hg_eq : (h r + Q * Real.log r / (2 * Real.pi * Tr)) -
        (h r0 + Q * Real.log r0 / (2 * Real.pi * Tr)) = 0 := by
      have h1 : ((h r + Q * Real.log r / (2 * Real.pi * Tr)) -
          (h r0 + Q * Real.log r0 / (2 * Real.pi * Tr))) / (r - r0) = 0 := by
        have := hc_eq.symm
        simpa using this
      have h2 := div_eq_zero_iff.mp h1
      rcases h2 with hnum | hden
      · exact hnum
      · exact absurd hden hrne
    have hlogdiv : Real.log (r / r0) = Real.log r - Real.log r0 :=
      Real.log_div hr' hr0'
    rw [hlogdiv]
    have hfield : h r - h r0 = -Q * (Real.log r - Real.log r0) / (2 * Real.pi * Tr) := by
      have h3 := hg_eq
      field_simp at h3 ⊢
      linarith
    exact hfield

/-- The radial Darcy profile solves the model for every discharge `Q`: at each radius `r > 0`
its radial derivative is `-Q / (2 π Tr r)`, and its outward discharge is `Q`. -/
lemma radialDarcyHead_solves {h0 Q Tr r0 r : ℝ} (hr0 : 0 < r0) (hTr : 0 < Tr) (hr : 0 < r) :
    HasDerivAt (radialDarcyHead h0 Q Tr r0) (-Q / (2 * Real.pi * Tr * r)) r ∧
      -2 * Real.pi * r * Tr * (-Q / (2 * Real.pi * Tr * r)) = Q := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hr0' : r0 ≠ 0 := ne_of_gt hr0
  have hr' : r ≠ 0 := ne_of_gt hr
  have hTr' : Tr ≠ 0 := ne_of_gt hTr
  constructor
  · have h1 : HasDerivAt (fun s : ℝ => s / r0) (1 / r0) r :=
      (hasDerivAt_id r).div_const r0
    have hne : r / r0 ≠ 0 := by
      apply ne_of_gt
      positivity
    have hlog : HasDerivAt (fun s : ℝ => Real.log (s / r0)) ((1 / r0) / (r / r0)) r :=
      h1.log hne
    have hQ : HasDerivAt (fun s : ℝ => Q * Real.log (s / r0)) (Q * ((1 / r0) / (r / r0))) r :=
      hlog.const_mul Q
    have hdiv : HasDerivAt (fun s : ℝ => Q * Real.log (s / r0) / (2 * Real.pi * Tr))
        ((Q * ((1 / r0) / (r / r0))) / (2 * Real.pi * Tr)) r :=
      hQ.div_const (2 * Real.pi * Tr)
    have hsub : HasDerivAt (fun s : ℝ => h0 - Q * Real.log (s / r0) / (2 * Real.pi * Tr))
        (-((Q * ((1 / r0) / (r / r0))) / (2 * Real.pi * Tr))) r :=
      hdiv.const_sub h0
    have heq :
        -((Q * ((1 / r0) / (r / r0))) / (2 * Real.pi * Tr)) = -Q / (2 * Real.pi * Tr * r) := by
      field_simp
    rw [heq] at hsub
    exact hsub
  · field_simp

/-! ## B. Matching the Thiem profile -/

/-- The Thiem rate is the pumping (extraction) rate: the Thiem profile
`C + P log r / (2 π Tr)` with rate `P` has radial derivative `P / (2 π Tr r)` at `r > 0`, so
its outward discharge `-2 π r Tr h'(r)` is `-P`. -/
lemma thiemProfile_outward_discharge {P Tr C r : ℝ} (hTr : 0 < Tr) (hr : 0 < r) :
    HasDerivAt (fun s => C + P * Real.log s / (2 * Real.pi * Tr))
        (P / (2 * Real.pi * Tr * r)) r ∧
      -2 * Real.pi * r * Tr * (P / (2 * Real.pi * Tr * r)) = -P := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hr' : r ≠ 0 := ne_of_gt hr
  have hTr' : Tr ≠ 0 := ne_of_gt hTr
  constructor
  · have hlog : HasDerivAt Real.log r⁻¹ r := Real.hasDerivAt_log hr'
    have hP : HasDerivAt (fun s : ℝ => P * Real.log s) (P * r⁻¹) r :=
      hlog.const_mul P
    have hdiv : HasDerivAt (fun s : ℝ => P * Real.log s / (2 * Real.pi * Tr))
        ((P * r⁻¹) / (2 * Real.pi * Tr)) r :=
      hP.div_const (2 * Real.pi * Tr)
    have hadd : HasDerivAt (fun s : ℝ => C + P * Real.log s / (2 * Real.pi * Tr))
        ((P * r⁻¹) / (2 * Real.pi * Tr)) r :=
      hdiv.const_add C
    have heq : (P * r⁻¹) / (2 * Real.pi * Tr) = P / (2 * Real.pi * Tr * r) := by
      field_simp
    rw [heq] at hadd
    exact hadd
  · field_simp

/-- Matching the Thiem profile with the sign reversed: on the annulus, the radial Darcy head
difference equals the Thiem head difference of `EarthScience.thiem_head_difference` for the
pumping rate `-Q`, with any additive constant `C`. -/
lemma radialDarcy_head_sub_eq_thiem {h h' : ℝ → ℝ} {Q Tr r0 r1 : ℝ} (hr0 : 0 < r0)
    (hTr : 0 < Tr) (hcont : ContinuousOn h (Set.Icc r0 r1))
    (hderiv : ∀ r ∈ Set.Ioo r0 r1, HasDerivAt h (h' r) r)
    (hQ : ∀ r ∈ Set.Ioo r0 r1, Q = -2 * Real.pi * r * Tr * h' r) (C : ℝ) :
    ∀ r ∈ Set.Icc r0 r1, h r - h r0 =
      (C + -Q * Real.log r / (2 * Real.pi * Tr)) -
        (C + -Q * Real.log r0 / (2 * Real.pi * Tr)) := by
  have hTr' : Tr ≠ 0 := ne_of_gt hTr
  intro r hr
  have hrpos : 0 < r := lt_of_lt_of_le hr0 hr.1
  have hmain : h r - h r0 = -Q * Real.log (r / r0) / (2 * Real.pi * Tr) :=
    radialDarcy_head_sub hr0 hTr hcont hderiv hQ r hr
  have hthiem : (C + -Q * Real.log r / (2 * Real.pi * Tr)) -
      (C + -Q * Real.log r0 / (2 * Real.pi * Tr)) =
      -Q * Real.log (r / r0) / (2 * Real.pi * Tr) :=
    thiem_head_difference hTr' hr0 hrpos
  exact hmain.trans hthiem.symm

/-! ## C. Rejected inputs -/

/-- A zero well radius is rejected: for `Tr > 0`, `r1 > 0` and a nonzero discharge `Q`, no head
continuous on `[0, r1]` satisfies the radial Darcy discharge relation on `(0, r1)`, because
the logarithmic profile is unbounded at the axis. -/
lemma radialDarcy_no_head_at_axis {h h' : ℝ → ℝ} {Q Tr r1 : ℝ} (hTr : 0 < Tr) (hr1 : 0 < r1)
    (hQ0 : Q ≠ 0) (hcont : ContinuousOn h (Set.Icc 0 r1))
    (hderiv : ∀ r ∈ Set.Ioo 0 r1, HasDerivAt h (h' r) r)
    (hQ : ∀ r ∈ Set.Ioo 0 r1, Q = -2 * Real.pi * r * Tr * h' r) :
    False := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have hMabs : ∀ x ∈ Set.Icc 0 r1, |h x| ≤ M := by
    intro x hx
    have hle := hM x hx
    rwa [Real.norm_eq_abs] at hle
  have h0mem : (0 : ℝ) ∈ Set.Icc 0 r1 := ⟨le_refl 0, le_of_lt hr1⟩
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hMabs 0 h0mem)
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hTr' : Tr ≠ 0 := ne_of_gt hTr
  have hQabs : 0 < |Q| := abs_pos.mpr hQ0
  have hQabs_ne : |Q| ≠ 0 := ne_of_gt hQabs
  have hden_pos : 0 < 2 * Real.pi * Tr := by positivity
  have hden_ne : (2 * Real.pi * Tr) ≠ 0 := ne_of_gt hden_pos
  set K : ℝ := (2 * M + 1) * (2 * Real.pi * Tr) / |Q| with hKdef
  have hKpos : 0 < K := by
    have h1 : 0 < 2 * M + 1 := by linarith
    have hnum : 0 < (2 * M + 1) * (2 * Real.pi * Tr) := mul_pos h1 hden_pos
    rw [hKdef]
    exact div_pos hnum hQabs
  have hexp_pos : 0 < Real.exp (-K) := Real.exp_pos _
  have hexp_ne : Real.exp (-K) ≠ 0 := ne_of_gt hexp_pos
  set r : ℝ := r1 * Real.exp (-K) with hrdef
  have hrpos : 0 < r := by
    rw [hrdef]
    exact mul_pos hr1 hexp_pos
  have hr0le : 0 ≤ r := le_of_lt hrpos
  have hexp_lt : Real.exp (-K) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hrr1 : r < r1 := by
    have hmul : r1 * Real.exp (-K) < r1 * 1 :=
      mul_lt_mul_of_pos_left hexp_lt hr1
    rw [mul_one] at hmul
    rw [hrdef]
    exact hmul
  have hrle : r ≤ r1 := le_of_lt hrr1
  have hrne : r ≠ 0 := ne_of_gt hrpos
  have hr1ne : r1 ≠ 0 := ne_of_gt hr1
  have hsubIcc : Set.Icc r r1 ⊆ Set.Icc 0 r1 :=
    Set.Icc_subset_Icc_left hr0le
  have hcont' : ContinuousOn h (Set.Icc r r1) := hcont.mono hsubIcc
  have hderiv' : ∀ s ∈ Set.Ioo r r1, HasDerivAt h (h' s) s := by
    intro s hs
    have hs0 : s ∈ Set.Ioo 0 r1 := ⟨lt_trans hrpos hs.1, hs.2⟩
    exact hderiv s hs0
  have hQ' : ∀ s ∈ Set.Ioo r r1, Q = -2 * Real.pi * s * Tr * h' s := by
    intro s hs
    have hs0 : s ∈ Set.Ioo 0 r1 := ⟨lt_trans hrpos hs.1, hs.2⟩
    exact hQ s hs0
  have hr1mem : r1 ∈ Set.Icc r r1 := ⟨hrle, le_refl r1⟩
  have hmain := radialDarcy_head_sub hrpos hTr hcont' hderiv' hQ' r1 hr1mem
  have hratio : r1 / r = Real.exp K := by
    rw [hrdef]
    have h1 : r1 / (r1 * Real.exp (-K)) = 1 / Real.exp (-K) := by field_simp
    rw [h1, Real.exp_neg, one_div, inv_inv]
  have hlog : Real.log (r1 / r) = K := by
    rw [hratio, Real.log_exp]
  rw [hlog] at hmain
  have habs : |h r1 - h r| = 2 * M + 1 := by
    rw [hmain]
    have h1 : |-Q * K / (2 * Real.pi * Tr)| = |Q| * K / (2 * Real.pi * Tr) := by
      rw [abs_div, abs_mul, abs_neg]
      have hk : |K| = K := abs_of_pos hKpos
      have hden : |2 * Real.pi * Tr| = 2 * Real.pi * Tr := abs_of_pos hden_pos
      rw [hk, hden]
    rw [h1, hKdef]
    field_simp
  have hmem1 : r1 ∈ Set.Icc 0 r1 := ⟨le_of_lt hr1, le_refl r1⟩
  have hmemr : r ∈ Set.Icc 0 r1 := ⟨hr0le, hrle⟩
  have hb1 : |h r1| ≤ M := hMabs r1 hmem1
  have hbr : |h r| ≤ M := hMabs r hmemr
  have hle := abs_sub_le (h r1) 0 (h r)
  simp only [sub_zero, zero_sub, abs_neg] at hle
  have htri : |h r1 - h r| ≤ 2 * M := by linarith
  linarith

/-- A negative transmissivity is rejected: for `Tr < 0`, at a radius `r > 0` where the head
gradient `h'` is nonzero, the discharge `-2 π r Tr h'` has the sign of `h'`, so the water
would flow toward higher head. -/
lemma radialDischarge_upgradient_of_neg {Tr r h' : ℝ} (hTr : Tr < 0) (hr : 0 < r)
    (hh' : h' ≠ 0) :
    0 < (-2 * Real.pi * r * Tr * h') * h' := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have h2 : 0 < h' ^ 2 := by
    rw [pow_two]
    exact mul_self_pos.mpr hh'
  have hTr' : 0 < -Tr := by linarith
  have h : (-2 * Real.pi * r * Tr * h') * h' = (2 * Real.pi * r * (-Tr)) * (h' ^ 2) := by ring
  rw [h]
  have hpos : 0 < 2 * Real.pi * r * (-Tr) := by positivity
  positivity

section WellLedger

open MathlibExt.Analysis.ODE.ContinuumBalances

/-! ## D. Cells with wells -/

/-- Cell rate of a finite-volume chain with wells: the transport rate
`discreteBalance Δx F i = -(F (i + 1) - F i) / Δx` of cell `i` plus its well source `q i / Δx`.
`Δx > 0` is the common cell volume, `F j` the signed flux through face `j` and `q i` the signed
well rate of cell `i` (injection `q i > 0`, production `q i < 0`). -/
noncomputable def wellCellRate {n : ℕ} (Δx : {x : ℝ // 0 < x}) (F : Fin (n + 1) → ℝ)
    (q : Fin n → ℝ) (i : Fin n) : ℝ :=
  discreteBalance Δx F i + q i / Δx

/-- Enthalpy flux through face `j`: the signed mass flux `Fm j` times the specific enthalpy
`specificEnthalpy (ef j) (pf j) (ρf j)` of the fluid crossing the face (flow work counted once,
inside the enthalpy). The face densities are positive (`_hρf`): at `ρ = 0` Lean's `x / 0 = 0`
would turn the enthalpy into `e` and drop the flow work. -/
noncomputable def faceEnthalpyFlux {n : ℕ} (Fm ef pf ρf : Fin (n + 1) → ℝ)
    (_hρf : ∀ j, 0 < ρf j) (j : Fin (n + 1)) : ℝ :=
  Fm j * ControlVolumes.specificEnthalpy (ef j) (pf j) (ρf j)

/-- Well energy rate of cell `i`: the injection rate `qI i` at the injected specific enthalpy
`hI i`, minus the production rate `qP i` at the cell's own specific enthalpy
`specificEnthalpy (ec i) (pc i) (ρc i)`. The signed well mass rate of the cell is `qI i - qP i`,
and the produced enthalpy leaves at the same production rate `qP i`. The cell densities are
positive (`_hρc`), as the face densities of `faceEnthalpyFlux`. -/
noncomputable def wellEnergyRate {n : ℕ} (qI qP hI ec pc ρc : Fin n → ℝ)
    (_hρc : ∀ i, 0 < ρc i) (i : Fin n) : ℝ :=
  qI i * hI i - qP i * ControlVolumes.specificEnthalpy (ec i) (pc i) (ρc i)

/-- **Finite-volume ledger with wells.** The cell rates sum to the transport total
`totalDiscreteChange Δx F` plus the well total over `Δx`, and one explicit step
`c i ↦ c i + dt * wellCellRate Δx F q i` changes the stock `Δx * ∑ i, c i` by `dt` times the net
boundary inflow `F 0 - F (Fin.last n)` plus the well total `∑ i, q i`. The exterior fluxes may
be nonzero; the interior fluxes cancel (`totalDiscreteChange_eq`). -/
lemma stock_add_mul_wellCellRate {n : ℕ} (Δx : {x : ℝ // 0 < x}) (dt : ℝ) (c : Fin n → ℝ)
    (F : Fin (n + 1) → ℝ) (q : Fin n → ℝ) :
    ∑ i, wellCellRate Δx F q i = totalDiscreteChange Δx F + (∑ i, q i) / Δx ∧
      Δx * ∑ i, (c i + dt * wellCellRate Δx F q i) =
        Δx * ∑ i, c i + dt * ((F 0 - F (Fin.last n)) + ∑ i, q i) := by
  have hΔx : (Δx : ℝ) ≠ 0 := ne_of_gt Δx.2
  have hsum : ∑ i, wellCellRate Δx F q i = totalDiscreteChange Δx F + (∑ i, q i) / Δx := by
    simp only [wellCellRate, totalDiscreteChange]
    rw [Finset.sum_add_distrib, ← Finset.sum_div]
  refine ⟨hsum, ?_⟩
  have hstep : ∑ i, (c i + dt * wellCellRate Δx F q i)
      = ∑ i, (c i + dt * (q i / Δx)) + dt * totalDiscreteChange Δx F := by
    rw [← sum_add_mul_discreteBalance Δx dt (fun i => c i + dt * (q i / Δx)) F]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [wellCellRate]
    ring
  rw [hstep, totalDiscreteChange_eq, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div]
  field_simp
  ring

/-! ## E. Mass and energy ledgers -/

/-- **Production enthalpy from the stored cell state.** If cell `i` stores the fluid mass
`m i = φ i * ρc i` per unit volume (porosity `φ i > 0`, fluid density `ρc i > 0`) and the fluid
energy `E i = m i * ec i` (specific internal energy `ec i`; no rock energy is stored), the
produced specific enthalpy `specificEnthalpy (ec i) (pc i) (ρc i) = ec i + pc i / ρc i` is
`(E i + φ i * pc i) / m i`, and the well energy rate is
`qI i * hI i - qP i * ((E i + φ i * pc i) / m i)`: the production withdrawal is fixed by the stored
mass and energy, the porosity and the cell pressure `pc i`. -/
lemma wellEnergyRate_eq_stored {n : ℕ} {m E qI qP hI ec pc ρc φ : Fin n → ℝ}
    (hρc : ∀ i, 0 < ρc i) (hφ : ∀ i, 0 < φ i) (hm : ∀ i, m i = φ i * ρc i)
    (hE : ∀ i, E i = m i * ec i) (i : Fin n) :
    wellEnergyRate qI qP hI ec pc ρc hρc i = qI i * hI i - qP i * ((E i + φ i * pc i) / m i) := by
  have hρ : ρc i ≠ 0 := ne_of_gt (hρc i)
  have hφ0 : φ i ≠ 0 := ne_of_gt (hφ i)
  simp only [wellEnergyRate, ControlVolumes.specificEnthalpy]
  rw [hE i, hm i]
  field_simp

/-- **Well and boundary sources in the energy ledger.** On a chain of `n` cells of common
positive volume `Δx`, with signed face mass fluxes `Fm` (one per face, shared by the mass and the
energy ledger) and positive face densities `ρf`, injection rates `qI` at specific enthalpies `hI`
and production rates `qP`: if each cell stores the fluid mass `m i = φ i * ρc i` (porosity
`φ i > 0`, fluid density `ρc i > 0`) and the fluid energy `E i = m i * ec i`, one explicit step of
the stored mass and energy changes the total mass by `dt ((Fm 0 - Fm n) + ∑ (qI - qP))` and the
total energy by `dt` times the net boundary enthalpy inflow plus `∑ (qI hI - qP h)`, where the
produced enthalpy `h = (E i + φ i * pc i) / m i` is that of the stored cell state. The face states
are free: the identity holds for every choice. -/
lemma well_boundary_ledger {n : ℕ} (Δx : {x : ℝ // 0 < x}) (dt : ℝ) (m E : Fin n → ℝ)
    (Fm ef pf ρf : Fin (n + 1) → ℝ) (qI qP hI ec pc ρc φ : Fin n → ℝ) (hρf : ∀ j, 0 < ρf j)
    (hρc : ∀ i, 0 < ρc i) (hφ : ∀ i, 0 < φ i) (hm : ∀ i, m i = φ i * ρc i)
    (hE : ∀ i, E i = m i * ec i) :
    Δx * ∑ i, (m i + dt * wellCellRate Δx Fm (fun i => qI i - qP i) i) =
        Δx * ∑ i, m i + dt * ((Fm 0 - Fm (Fin.last n)) + ∑ i, (qI i - qP i)) ∧
      Δx * ∑ i, (E i + dt * wellCellRate Δx (faceEnthalpyFlux Fm ef pf ρf hρf)
          (wellEnergyRate qI qP hI ec pc ρc hρc) i) =
        Δx * ∑ i, E i + dt * ((faceEnthalpyFlux Fm ef pf ρf hρf 0 -
          faceEnthalpyFlux Fm ef pf ρf hρf (Fin.last n)) +
            ∑ i, (qI i * hI i - qP i * ((E i + φ i * pc i) / m i))) := by
  refine ⟨(stock_add_mul_wellCellRate Δx dt m Fm (fun i => qI i - qP i)).2, ?_⟩
  rw [(stock_add_mul_wellCellRate Δx dt E (faceEnthalpyFlux Fm ef pf ρf hρf)
      (wellEnergyRate qI qP hI ec pc ρc hρc)).2,
    Finset.sum_congr rfl fun i _ => wellEnergyRate_eq_stored hρc hφ hm hE i]

end WellLedger

section FractionalFlow

open MathlibExt.Analysis.ODE.ContinuumBalances

/-! ## F. Fractional flow -/

private lemma denom_pos {μo μw s : ℝ} (hμo : 0 < μo) (hμw : 0 < μw) :
    0 < μo * s ^ 2 + μw * (1 - s) ^ 2 := by
  have h1 : 0 ≤ μo * s ^ 2 := by positivity
  have h2 : 0 ≤ μw * (1 - s) ^ 2 := by positivity
  by_cases hs : s = 0
  · subst hs
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      zero_add]
    have : (0 : ℝ) < μw * 1 := by positivity
    simpa using this
  · have hs2 : 0 < s ^ 2 := by positivity
    have hpos : 0 < μo * s ^ 2 := mul_pos hμo hs2
    linarith

/-- Water fractional flow `μo s ^ 2 / (μo s ^ 2 + μw (1 - s) ^ 2)` at normalized saturation `s`,
from the relative permeabilities `s ^ 2` (water) and `(1 - s) ^ 2` (oil) and the oil and water
viscosities `μo`, `μw`. -/
noncomputable def fracFlow (μo μw s : ℝ) : ℝ :=
  μo * s ^ 2 / (μo * s ^ 2 + μw * (1 - s) ^ 2)

/-- Derivative of the fractional flow: `2 μo μw s (1 - s) / (μo s ^ 2 + μw (1 - s) ^ 2) ^ 2`. -/
noncomputable def fracFlowDeriv (μo μw s : ℝ) : ℝ :=
  2 * μo * μw * s * (1 - s) / (μo * s ^ 2 + μw * (1 - s) ^ 2) ^ 2

/-- Derivative bound `B = (μo + μw) ^ 2 / (2 μo μw)` of the fractional flow on `[0, 1]`. -/
noncomputable def fracFlowBound (μo μw : ℝ) : ℝ :=
  (μo + μw) ^ 2 / (2 * μo * μw)

private lemma fracFlowBound_pos {μo μw : ℝ} (hμo : 0 < μo) (hμw : 0 < μw) :
    0 < fracFlowBound μo μw := by
  simp only [fracFlowBound]
  positivity

/-- Endpoint values: no water flows at connate water, `f 0 = 0`, and only water flows at
residual oil, `f 1 = 1`. -/
lemma fracFlow_zero_one {μo : ℝ} (μw : ℝ) (hμo : 0 < μo) :
    fracFlow μo μw 0 = 0 ∧ fracFlow μo μw 1 = 1 := by
  have hμo' : μo ≠ 0 := ne_of_gt hμo
  constructor
  · simp [fracFlow]
  · simp [fracFlow, hμo']

/-- The fractional flow has derivative `fracFlowDeriv μo μw s` at every `s`, for positive
viscosities (the denominator never vanishes). -/
lemma hasDerivAt_fracFlow {μo μw : ℝ} (hμo : 0 < μo) (hμw : 0 < μw) (s : ℝ) :
    HasDerivAt (fracFlow μo μw) (fracFlowDeriv μo μw s) s := by
  have hDpos : 0 < μo * s ^ 2 + μw * (1 - s) ^ 2 := denom_pos hμo hμw
  have hDne : μo * s ^ 2 + μw * (1 - s) ^ 2 ≠ 0 := ne_of_gt hDpos
  have hPow : HasDerivAt (fun x : ℝ => x ^ 2) (2 * s) s := by
    simpa using hasDerivAt_pow 2 s
  have hN : HasDerivAt (fun x : ℝ => μo * x ^ 2) (μo * (2 * s)) s :=
    HasDerivAt.const_mul μo hPow
  have hSub : HasDerivAt (fun x : ℝ => 1 - x) (-1) s := by
    have h1 : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 s := hasDerivAt_const s 1
    have h2 : HasDerivAt (fun x : ℝ => x) 1 s := hasDerivAt_id s
    have h := HasDerivAt.sub h1 h2
    have hEq : (fun x : ℝ => 1 - x) = (fun _ : ℝ => (1 : ℝ)) - (fun x : ℝ => x) := by
      funext x
      rfl
    have hEq2 : (-1 : ℝ) = 0 - 1 := by norm_num
    rw [hEq, hEq2]
    exact h
  have hPow2 : HasDerivAt (fun x : ℝ => (1 - x) ^ 2) (2 * (1 - s) * (-1)) s := by
    have h := HasDerivAt.pow hSub 2
    have hEq : (fun x : ℝ => (1 - x) ^ 2) = ((fun x : ℝ => 1 - x) ^ 2) := by
      funext x
      rfl
    have hDeriv : (2 : ℝ) * (1 - s) * (-1) = 2 * (1 - s) ^ (2 - 1) * (-1) := by
      norm_num
    rw [hEq, hDeriv]
    exact h
  have hM : HasDerivAt (fun x : ℝ => μw * (1 - x) ^ 2) (μw * (2 * (1 - s) * (-1))) s :=
    HasDerivAt.const_mul μw hPow2
  have hD : HasDerivAt (fun x : ℝ => μo * x ^ 2 + μw * (1 - x) ^ 2)
      (μo * (2 * s) + μw * (2 * (1 - s) * (-1))) s := by
    have h := HasDerivAt.add hN hM
    have hEq : (fun x : ℝ => μo * x ^ 2 + μw * (1 - x) ^ 2)
        = (fun x : ℝ => μo * x ^ 2) + (fun x : ℝ => μw * (1 - x) ^ 2) := by
      funext x
      rfl
    rw [hEq]
    exact h
  have hDiv := HasDerivAt.div hN hD hDne
  have hEq : fracFlow μo μw
      = (fun x : ℝ => μo * x ^ 2) / (fun x : ℝ => μo * x ^ 2 + μw * (1 - x) ^ 2) := by
    funext x
    rfl
  have hDeriv : fracFlowDeriv μo μw s
      = (μo * (2 * s) * (μo * s ^ 2 + μw * (1 - s) ^ 2)
          - μo * s ^ 2 * (μo * (2 * s) + μw * (2 * (1 - s) * (-1))))
        / (μo * s ^ 2 + μw * (1 - s) ^ 2) ^ 2 := by
    simp only [fracFlowDeriv]
    ring
  rw [hEq, hDeriv]
  exact hDiv

/-- Finite derivative bound: on `[0, 1]` the derivative lies in `[0, B]`,
`B = (μo + μw) ^ 2 / (2 μo μw)`. -/
lemma fracFlowDeriv_mem_Icc {μo μw s : ℝ} (hμo : 0 < μo) (hμw : 0 < μw)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    fracFlowDeriv μo μw s ∈ Set.Icc 0 (fracFlowBound μo μw) := by
  obtain ⟨hs0, hs1⟩ := hs
  have hDpos : 0 < μo * s ^ 2 + μw * (1 - s) ^ 2 := denom_pos hμo hμw
  have hD2pos : 0 < (μo * s ^ 2 + μw * (1 - s) ^ 2) ^ 2 := by positivity
  have h1s : 0 ≤ (1 : ℝ) - s := by linarith
  have hNum : 0 ≤ 2 * μo * μw * s * (1 - s) := by positivity
  have hLower : 0 ≤ fracFlowDeriv μo μw s := by
    simp only [fracFlowDeriv]
    exact div_nonneg hNum (le_of_lt hD2pos)
  have hSumPos : 0 < μo + μw := add_pos hμo hμw
  have hId : (μo + μw) * (μo * s ^ 2 + μw * (1 - s) ^ 2)
      = μo * μw + (μo * s - μw * (1 - s)) ^ 2 := by ring
  have hSq : 0 ≤ (μo * s - μw * (1 - s)) ^ 2 := sq_nonneg _
  have hMulGe : μo * μw ≤ (μo * s ^ 2 + μw * (1 - s) ^ 2) * (μo + μw) := by
    have h' : μo * μw ≤ (μo + μw) * (μo * s ^ 2 + μw * (1 - s) ^ 2) := by
      rw [hId]
      exact le_add_of_nonneg_right hSq
    rw [mul_comm (μo * s ^ 2 + μw * (1 - s) ^ 2) (μo + μw)]
    exact h'
  have hDge : μo * μw / (μo + μw) ≤ μo * s ^ 2 + μw * (1 - s) ^ 2 := by
    rw [div_le_iff₀ hSumPos]
    exact hMulGe
  have hD0nonneg : 0 ≤ μo * μw / (μo + μw) := by positivity
  have hD2ge : (μo * μw / (μo + μw)) ^ 2 ≤ (μo * s ^ 2 + μw * (1 - s) ^ 2) ^ 2 := by
    nlinarith [hDge, hD0nonneg, hDpos,
      sq_nonneg (μo * s ^ 2 + μw * (1 - s) ^ 2 - μo * μw / (μo + μw))]
  have hBpos : 0 < fracFlowBound μo μw := fracFlowBound_pos hμo hμw
  have hBmono : fracFlowBound μo μw * (μo * μw / (μo + μw)) ^ 2
      ≤ fracFlowBound μo μw * (μo * s ^ 2 + μw * (1 - s) ^ 2) ^ 2 :=
    mul_le_mul_of_nonneg_left hD2ge (le_of_lt hBpos)
  have hμo' : μo ≠ 0 := ne_of_gt hμo
  have hμw' : μw ≠ 0 := ne_of_gt hμw
  have hSumNe : μo + μw ≠ 0 := ne_of_gt hSumPos
  have hBD0 : fracFlowBound μo μw * (μo * μw / (μo + μw)) ^ 2 = μo * μw / 2 := by
    simp only [fracFlowBound]
    field_simp
  have hS : s * (1 - s) ≤ 1 / 4 := by
    nlinarith [sq_nonneg (s - 1 / 2)]
  have hμwμo : 0 ≤ μo * μw := by positivity
  have hNle : 2 * μo * μw * s * (1 - s) ≤ μo * μw / 2 := by
    have h2 : 2 * (s * (1 - s)) ≤ 1 / 2 := by linarith
    have hEq1 : 2 * μo * μw * s * (1 - s) = (μo * μw) * (2 * (s * (1 - s))) := by ring
    have hEq2 : μo * μw / 2 = (μo * μw) * (1 / 2) := by ring
    rw [hEq1, hEq2]
    exact mul_le_mul_of_nonneg_left h2 hμwμo
  have hNleB : 2 * μo * μw * s * (1 - s)
      ≤ fracFlowBound μo μw * (μo * s ^ 2 + μw * (1 - s) ^ 2) ^ 2 := by
    calc 2 * μo * μw * s * (1 - s) ≤ μo * μw / 2 := hNle
      _ = fracFlowBound μo μw * (μo * μw / (μo + μw)) ^ 2 := hBD0.symm
      _ ≤ fracFlowBound μo μw * (μo * s ^ 2 + μw * (1 - s) ^ 2) ^ 2 := hBmono
  have hUpper : fracFlowDeriv μo μw s ≤ fracFlowBound μo μw := by
    simp only [fracFlowDeriv]
    rw [div_le_iff₀ hD2pos]
    exact hNleB
  exact ⟨hLower, hUpper⟩

/-- Lipschitz bound with monotone increment: for `t ≤ s` in `[0, 1]`,
`0 ≤ f s - f t ≤ B (s - t)`. -/
lemma fracFlow_sub_mem_Icc {μo μw s t : ℝ} (hμo : 0 < μo) (hμw : 0 < μw)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) (hts : t ≤ s) :
    fracFlow μo μw s - fracFlow μo μw t ∈ Set.Icc 0 (fracFlowBound μo μw * (s - t)) := by
  rcases eq_or_lt_of_le hts with hEq | hLt
  · subst hEq
    simp
  · have hCont : ContinuousOn (fracFlow μo μw) (Set.Icc t s) := fun x _ =>
      (hasDerivAt_fracFlow hμo hμw x).continuousAt.continuousWithinAt
    have hDeriv : ∀ x ∈ Set.Ioo t s,
        HasDerivAt (fracFlow μo μw) (fracFlowDeriv μo μw x) x :=
      fun x _ => hasDerivAt_fracFlow hμo hμw x
    obtain ⟨c, hcMem, hcEq⟩ := exists_hasDerivAt_eq_slope
      (fracFlow μo μw) (fracFlowDeriv μo μw) hLt hCont hDeriv
    have hc01 : c ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨le_trans ht.1 (le_of_lt hcMem.1), le_trans (le_of_lt hcMem.2) hs.2⟩
    obtain ⟨hLo, hHi⟩ := fracFlowDeriv_mem_Icc hμo hμw hc01
    have hPos : 0 < s - t := sub_pos.mpr hLt
    have hNe : s - t ≠ 0 := ne_of_gt hPos
    have hEq : fracFlowDeriv μo μw c * (s - t)
        = fracFlow μo μw s - fracFlow μo μw t := by
      rw [hcEq, div_mul_cancel₀ _ hNe]
    have hNonneg : 0 ≤ s - t := le_of_lt hPos
    have hLower : 0 ≤ fracFlow μo μw s - fracFlow μo μw t := by
      rw [← hEq]
      exact mul_nonneg hLo hNonneg
    have hUpper : fracFlow μo μw s - fracFlow μo μw t
        ≤ fracFlowBound μo μw * (s - t) := by
      rw [← hEq]
      exact mul_le_mul_of_nonneg_right hHi hNonneg
    exact ⟨hLower, hUpper⟩

/-- Monotonicity of the fractional flow on `[0, 1]`. -/
lemma monotoneOn_fracFlow {μo μw : ℝ} (hμo : 0 < μo) (hμw : 0 < μw) :
    MonotoneOn (fracFlow μo μw) (Set.Icc 0 1) := by
  intro a ha b hb hab
  have h := (fracFlow_sub_mem_Icc hμo hμw hb ha hab).1
  linarith

/-! ## G. Normalized saturation and the CFL number -/

/-- Normalized saturation `s = (S - Swc) / ΔS` on the mobile range, `ΔS = 1 - Sor - Swc`. -/
noncomputable def normSat (Swc Sor S : ℝ) : ℝ :=
  (S - Swc) / (1 - Sor - Swc)

/-- CFL number of the normalized update, `ν = Q dt / (φ A dx ΔS)`. -/
noncomputable def cflNumber (Q dt φ A dx ΔS : ℝ) : ℝ :=
  Q * dt / (φ * A * dx * ΔS)

/-- For `ΔS > 0` the normalized saturation lies in `[0, 1]` exactly when `S ∈ [Swc, 1 - Sor]`. -/
lemma normSat_mem_Icc_iff {Swc Sor : ℝ} (hΔS : 0 < 1 - Sor - Swc) (S : ℝ) :
    normSat Swc Sor S ∈ Set.Icc 0 1 ↔ S ∈ Set.Icc Swc (1 - Sor) := by
  simp only [normSat, Set.mem_Icc]
  rw [le_div_iff₀ hΔS, div_le_iff₀ hΔS, zero_mul, one_mul]
  constructor
  · intro h
    obtain ⟨h0, h1⟩ := h
    constructor <;> linarith
  · intro h
    obtain ⟨h0, h1⟩ := h
    constructor <;> linarith

/-! ## H. The upwind step: monotonicity, interval and balance -/

/-- Local upwind update of a cell with normalized saturation `a` whose left neighbor (upwind
state) is `b`: `a - ν (f a - f b)`. -/
noncomputable def upwindUpdate (μo μw ν a b : ℝ) : ℝ :=
  a - ν * (fracFlow μo μw a - fracFlow μo μw b)

/-- One normalized upwind step on the chain `s : Fin (n + 1) → ℝ` with inflow state `sIn` at the
left boundary: cell `i` uses `Matrix.vecCons sIn s i.castSucc`, which is `sIn` for the first cell
and `s (i - 1)` otherwise. -/
noncomputable def upwindStep (μo μw ν sIn : ℝ) {n : ℕ} (s : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) : ℝ :=
  upwindUpdate μo μw ν (s i) (Matrix.vecCons sIn s i.castSucc)

/-- One physical step of the water saturations `S` with inflow saturation `Sin`: the water volume
of cell `i` changes by `Q dt (f s_(i-1) - f s_i)`, so `S i` changes by that amount over the pore
volume `φ A dx`. -/
noncomputable def satStep (μo μw Swc Sor Q dt φ A dx Sin : ℝ) {n : ℕ} (S : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) : ℝ :=
  S i - Q * dt / (φ * A * dx) * (fracFlow μo μw (normSat Swc Sor (S i)) -
    fracFlow μo μw (normSat Swc Sor (Matrix.vecCons Sin S i.castSucc)))

/-- **Monotone scheme.** Under `0 ≤ ν B ≤ 1` the update `a - ν (f a - f b)` is nondecreasing in
the cell state `a` and in the upwind state `b` on `[0, 1]`. -/
lemma upwindUpdate_mono {μo μw ν a a' b b' : ℝ} (hμo : 0 < μo) (hμw : 0 < μw)
    (hν0 : 0 ≤ ν * fracFlowBound μo μw) (hν1 : ν * fracFlowBound μo μw ≤ 1)
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (ha' : a' ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (hb' : b' ∈ Set.Icc (0 : ℝ) 1) (haa' : a ≤ a') (hbb' : b ≤ b') :
    upwindUpdate μo μw ν a b ≤ upwindUpdate μo μw ν a' b' := by
  have hBpos : 0 < fracFlowBound μo μw := fracFlowBound_pos hμo hμw
  have hν : 0 ≤ ν := nonneg_of_mul_nonneg_left hν0 hBpos
  obtain ⟨_, hDaB⟩ := fracFlow_sub_mem_Icc hμo hμw ha' ha haa'
  obtain ⟨hDb0, _⟩ := fracFlow_sub_mem_Icc hμo hμw hb' hb hbb'
  have hΔa : 0 ≤ a' - a := sub_nonneg.mpr haa'
  have hνDb : 0 ≤ ν * (fracFlow μo μw b' - fracFlow μo μw b) :=
    mul_nonneg hν hDb0
  have hνDa_le : ν * (fracFlow μo μw a' - fracFlow μo μw a)
      ≤ ν * (fracFlowBound μo μw * (a' - a)) :=
    mul_le_mul_of_nonneg_left hDaB hν
  have hνB : ν * (fracFlowBound μo μw * (a' - a))
      = (ν * fracFlowBound μo μw) * (a' - a) := by ring
  have hνB_le : (ν * fracFlowBound μo μw) * (a' - a) ≤ 1 * (a' - a) :=
    mul_le_mul_of_nonneg_right hν1 hΔa
  have hνDa_le_Δ : ν * (fracFlow μo μw a' - fracFlow μo μw a) ≤ a' - a := by
    calc ν * (fracFlow μo μw a' - fracFlow μo μw a)
        ≤ ν * (fracFlowBound μo μw * (a' - a)) := hνDa_le
      _ = (ν * fracFlowBound μo μw) * (a' - a) := hνB
      _ ≤ 1 * (a' - a) := hνB_le
      _ = a' - a := one_mul _
  simp only [upwindUpdate]
  have heq : ν * (fracFlow μo μw a' - fracFlow μo μw b')
      - ν * (fracFlow μo μw a - fracFlow μo μw b)
      = ν * (fracFlow μo μw a' - fracFlow μo μw a)
        - ν * (fracFlow μo μw b' - fracFlow μo μw b) := by ring
  linarith [hνDa_le_Δ, hνDb, heq]

/-- **Interval preservation.** If the inflow state and every cell lie in `[0, 1]` and
`0 ≤ ν B ≤ 1`, every cell of the upwind step lies in `[0, 1]`. -/
lemma upwindStep_mem_Icc {μo μw ν sIn : ℝ} {n : ℕ} {s : Fin (n + 1) → ℝ} (hμo : 0 < μo)
    (hμw : 0 < μw) (hν0 : 0 ≤ ν * fracFlowBound μo μw) (hν1 : ν * fracFlowBound μo μw ≤ 1)
    (hIn : sIn ∈ Set.Icc (0 : ℝ) 1) (hs : ∀ i, s i ∈ Set.Icc (0 : ℝ) 1) (i : Fin (n + 1)) :
    upwindStep μo μw ν sIn s i ∈ Set.Icc 0 1 := by
  have hUp : Matrix.vecCons sIn s i.castSucc ∈ Set.Icc (0 : ℝ) 1 := by
    have hAll : ∀ k : Fin (n + 2), Matrix.vecCons sIn s k ∈ Set.Icc (0 : ℝ) 1 := by
      intro k
      cases k using Fin.cases with
      | zero =>
        simpa [Matrix.cons_val_zero] using hIn
      | succ j =>
        simpa [Matrix.cons_val_succ] using hs j
    exact hAll _
  have h0 : fracFlow μo μw 0 = 0 := (fracFlow_zero_one μw hμo).1
  have h1 : fracFlow μo μw 1 = 1 := (fracFlow_zero_one μw hμo).2
  have h00 : upwindUpdate μo μw ν 0 0 = 0 := by simp [upwindUpdate, h0]
  have h11 : upwindUpdate μo μw ν 1 1 = 1 := by simp [upwindUpdate, h1]
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1mem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hLo : upwindUpdate μo μw ν 0 0
      ≤ upwindUpdate μo μw ν (s i) (Matrix.vecCons sIn s i.castSucc) :=
    upwindUpdate_mono hμo hμw hν0 hν1 h0mem (hs i) h0mem hUp (hs i).1 hUp.1
  have hHi : upwindUpdate μo μw ν (s i) (Matrix.vecCons sIn s i.castSucc)
      ≤ upwindUpdate μo μw ν 1 1 :=
    upwindUpdate_mono hμo hμw hν0 hν1 (hs i) h1mem hUp h1mem (hs i).2 hUp.2
  rw [h00] at hLo
  rw [h11] at hHi
  exact ⟨hLo, hHi⟩

/-- **Rescaling.** The physical step normalizes to the upwind step with the CFL number
`ν = Q dt / (φ A dx ΔS)`, `ΔS = 1 - Sor - Swc`, and the normalized inflow state. -/
lemma normSat_satStep (μo μw Swc Sor Q dt φ A dx Sin : ℝ) {n : ℕ} (S : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) :
    normSat Swc Sor (satStep μo μw Swc Sor Q dt φ A dx Sin S i) =
      upwindStep μo μw (cflNumber Q dt φ A dx (1 - Sor - Swc)) (normSat Swc Sor Sin)
        (fun j => normSat Swc Sor (S j)) i := by
  have hVec : ∀ k : Fin (n + 2), normSat Swc Sor (Matrix.vecCons Sin S k)
      = Matrix.vecCons (normSat Swc Sor Sin) (fun j => normSat Swc Sor (S j)) k := by
    intro k
    cases k using Fin.cases with
    | zero => simp [Matrix.cons_val_zero]
    | succ j => simp [Matrix.cons_val_succ]
  have hRing : ∀ (S Swc Q dt pv ΔS Δf : ℝ),
      (S - Q * dt / pv * Δf - Swc) / ΔS
        = (S - Swc) / ΔS - (Q * dt / (pv * ΔS)) * Δf := by
    intro S Swc Q dt pv ΔS Δf
    ring
  simp only [satStep, upwindStep, upwindUpdate, cflNumber]
  rw [← hVec i.castSucc]
  simp only [normSat]
  exact hRing _ _ _ _ _ _ _

/-- **Interval preservation for the saturations.** With positive viscosities, `ΔS > 0`,
positive pore volume, `Q ≥ 0`, `dt ≥ 0` and the evaluated CFL bound `ν B ≤ 1` for
`ν = Q dt / (φ A dx ΔS)`, a step from saturations in `[Swc, 1 - Sor]` with inflow saturation in
that range stays in `[Swc, 1 - Sor]`. -/
lemma satStep_mem_Icc {μo μw Swc Sor Q dt φ A dx Sin : ℝ} {n : ℕ} {S : Fin (n + 1) → ℝ}
    (hμo : 0 < μo) (hμw : 0 < μw) (hΔS : 0 < 1 - Sor - Swc) (hpv : 0 < φ * A * dx)
    (hQ : 0 ≤ Q) (hdt : 0 ≤ dt)
    (hcfl : cflNumber Q dt φ A dx (1 - Sor - Swc) * fracFlowBound μo μw ≤ 1)
    (hIn : Sin ∈ Set.Icc Swc (1 - Sor)) (hS : ∀ i, S i ∈ Set.Icc Swc (1 - Sor))
    (i : Fin (n + 1)) :
    satStep μo μw Swc Sor Q dt φ A dx Sin S i ∈ Set.Icc Swc (1 - Sor) := by
  have hBpos : 0 < fracFlowBound μo μw := fracFlowBound_pos hμo hμw
  have hνnonneg : 0 ≤ cflNumber Q dt φ A dx (1 - Sor - Swc) := by
    simp only [cflNumber]
    exact div_nonneg (mul_nonneg hQ hdt) (le_of_lt (mul_pos hpv hΔS))
  have hν0 : 0 ≤ cflNumber Q dt φ A dx (1 - Sor - Swc) * fracFlowBound μo μw :=
    mul_nonneg hνnonneg (le_of_lt hBpos)
  have hInN : normSat Swc Sor Sin ∈ Set.Icc (0 : ℝ) 1 :=
    (normSat_mem_Icc_iff hΔS _).mpr hIn
  have hSN : ∀ j, (fun j => normSat Swc Sor (S j)) j ∈ Set.Icc (0 : ℝ) 1 :=
    fun j => (normSat_mem_Icc_iff hΔS _).mpr (hS j)
  have hUp := upwindStep_mem_Icc hμo hμw hν0 hcfl hInN hSN i
  have hNorm : normSat Swc Sor (satStep μo μw Swc Sor Q dt φ A dx Sin S i)
      ∈ Set.Icc (0 : ℝ) 1 := by
    rw [normSat_satStep]
    exact hUp
  exact (normSat_mem_Icc_iff hΔS _).mp hNorm

/-- **Conservative form.** The upwind step is the finite-volume step with unit cell width and
time step `ν` for the face fluxes `f (Matrix.vecCons sIn s j)`: face `j` carries the fractional
flow of its left (upwind) state, the inflow state at the boundary face `0`. -/
lemma upwindStep_eq_discreteBalance (μo μw ν sIn : ℝ) {n : ℕ} (s : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) :
    upwindStep μo μw ν sIn s i =
      s i + ν * discreteBalance ⟨1, one_pos⟩
        (fun j => fracFlow μo μw (Matrix.vecCons sIn s j)) i := by
  have hSucc : Matrix.vecCons sIn s i.succ = s i := Matrix.cons_val_succ _ _ _
  simp only [upwindStep, upwindUpdate, discreteBalance, hSucc]
  ring

/-- **Inlet-minus-outlet balance (normalized).** The interior fluxes cancel: the sum of the
normalized saturations changes by `ν (f sIn - f s_out)`, `s_out = s (Fin.last n)` the outlet
cell. -/
lemma sum_upwindStep (μo μw ν sIn : ℝ) {n : ℕ} (s : Fin (n + 1) → ℝ) :
    ∑ i, upwindStep μo μw ν sIn s i =
      ∑ i, s i + ν * (fracFlow μo μw sIn - fracFlow μo μw (s (Fin.last n))) := by
  have hF0 : fracFlow μo μw (Matrix.vecCons sIn s 0) = fracFlow μo μw sIn := by
    rw [Matrix.cons_val_zero]
  have hLast : Fin.last (n + 1) = (Fin.last n).succ := (Fin.succ_last n).symm
  have hFlast : fracFlow μo μw (Matrix.vecCons sIn s (Fin.last (n + 1)))
      = fracFlow μo μw (s (Fin.last n)) := by
    rw [hLast, Matrix.cons_val_succ]
  simp only [upwindStep_eq_discreteBalance]
  rw [sum_add_mul_discreteBalance, totalDiscreteChange_eq, hF0, hFlast]
  ring

/-- **Inlet-minus-outlet water volume balance.** For positive pore volume `φ A dx`, one physical
step changes the water volume `φ A dx ∑ i, S i` by the inlet water volume `Q dt f (s_in)` minus
the outlet water volume `Q dt f (s_out)`. -/
lemma satStep_volume_balance {μo μw Swc Sor Q dt φ A dx Sin : ℝ} {n : ℕ} (S : Fin (n + 1) → ℝ)
    (hpv : 0 < φ * A * dx) :
    φ * A * dx * ∑ i, satStep μo μw Swc Sor Q dt φ A dx Sin S i =
      φ * A * dx * ∑ i, S i + Q * dt * (fracFlow μo μw (normSat Swc Sor Sin) -
        fracFlow μo μw (normSat Swc Sor (S (Fin.last n)))) := by
  have hpvne : φ * A * dx ≠ 0 := ne_of_gt hpv
  have hEq : ∀ i : Fin (n + 1), satStep μo μw Swc Sor Q dt φ A dx Sin S i
      = S i + (Q * dt / (φ * A * dx)) * discreteBalance ⟨1, one_pos⟩
        (fun j => fracFlow μo μw (normSat Swc Sor (Matrix.vecCons Sin S j))) i := by
    intro i
    have hSucc : Matrix.vecCons Sin S i.succ = S i := Matrix.cons_val_succ _ _ _
    simp only [satStep, discreteBalance, hSucc]
    ring
  have hF0 : fracFlow μo μw (normSat Swc Sor (Matrix.vecCons Sin S 0))
      = fracFlow μo μw (normSat Swc Sor Sin) := by
    rw [Matrix.cons_val_zero]
  have hLast : Fin.last (n + 1) = (Fin.last n).succ := (Fin.succ_last n).symm
  have hFlast : fracFlow μo μw (normSat Swc Sor (Matrix.vecCons Sin S (Fin.last (n + 1))))
      = fracFlow μo μw (normSat Swc Sor (S (Fin.last n))) := by
    rw [hLast, Matrix.cons_val_succ]
  have hSum : ∑ i, satStep μo μw Swc Sor Q dt φ A dx Sin S i
      = ∑ i, S i + (Q * dt / (φ * A * dx)) * totalDiscreteChange ⟨1, one_pos⟩
        (fun j => fracFlow μo μw (normSat Swc Sor (Matrix.vecCons Sin S j))) := by
    simp only [hEq]
    rw [sum_add_mul_discreteBalance]
  have hTotal : totalDiscreteChange ⟨1, one_pos⟩
        (fun j => fracFlow μo μw (normSat Swc Sor (Matrix.vecCons Sin S j)))
      = fracFlow μo μw (normSat Swc Sor Sin)
        - fracFlow μo μw (normSat Swc Sor (S (Fin.last n))) := by
    rw [totalDiscreteChange_eq, hF0, hFlast]
    ring
  rw [hTotal] at hSum
  have hED : φ * A * dx * (Q * dt / (φ * A * dx)) = Q * dt := by
    rw [mul_comm (φ * A * dx) (Q * dt / (φ * A * dx)), div_mul_cancel₀ _ hpvne]
  calc φ * A * dx * ∑ i, satStep μo μw Swc Sor Q dt φ A dx Sin S i
      = φ * A * dx * (∑ i, S i + (Q * dt / (φ * A * dx))
        * (fracFlow μo μw (normSat Swc Sor Sin)
          - fracFlow μo μw (normSat Swc Sor (S (Fin.last n))))) := by rw [hSum]
    _ = φ * A * dx * ∑ i, S i + Q * dt * (fracFlow μo μw (normSat Swc Sor Sin)
        - fracFlow μo μw (normSat Swc Sor (S (Fin.last n)))) := by
      rw [mul_add]
      congr 1
      calc φ * A * dx * ((Q * dt / (φ * A * dx))
            * (fracFlow μo μw (normSat Swc Sor Sin)
              - fracFlow μo μw (normSat Swc Sor (S (Fin.last n)))))
          = (φ * A * dx * (Q * dt / (φ * A * dx)))
            * (fracFlow μo μw (normSat Swc Sor Sin)
              - fracFlow μo μw (normSat Swc Sor (S (Fin.last n)))) := by ring
        _ = Q * dt * (fracFlow μo μw (normSat Swc Sor Sin)
            - fracFlow μo μw (normSat Swc Sor (S (Fin.last n)))) := by rw [hED]

end FractionalFlow

end EarthScience
